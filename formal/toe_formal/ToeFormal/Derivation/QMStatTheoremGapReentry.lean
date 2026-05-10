/-
ToeFormal/Derivation/QMStatTheoremGapReentry.lean

Bounded QM-STAT theorem-gap re-entry preparation.

Scope:
- consume `prepare_qm_stat_theorem_gap_reentry`
- consume `FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_SAMPLEREP32_AXIOM_AUDIT`
- identify exactly one bounded QM-STAT theorem-gap item
- select the target STAT entropy semantics obligation as the re-entry item
- record current authority and intended stronger authority
- rotate only to `review_qm_stat_theorem_gap_reentry_result`
- make no theorem discharge, pillar completion, seam closure, Phase 2
  readiness, empirical adequacy, canonical ToE status, master-action
  promotion, QFT-GR source-map closure, or governance-manifest enrollment
- do not enroll this focused packet gate in the governance manifest
-/

import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit
import ToeFormal.Derivation.QMSTATSourceProbabilityExtractionResultReview

namespace ToeFormal
namespace Derivation
namespace QMStatTheoremGapReentry

open CrossPillarClosureFrontier
open CrossPillarDerivationProtocol
open FullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAudit
open QMSTATSourceProbabilityExtractionResultReview
open QMSTATTransportSemanticsRetainedBlockerProtocolRow
open ToeFormal.Bridges.QMSTATTransportResidualPackage

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the QM-STAT theorem-gap re-entry preparation packet. -/
def qmStatTheoremGapReentrySurfaceId : String :=
  "qm_stat_theorem_gap_reentry_v0"

/-- The live target consumed by this re-entry preparation packet. -/
def qmStatTheoremGapReentryConsumedTargetId : String :=
  selectedFullPillarTargetMapNextTargetAfterSampleRep32AxiomAuditV0

/-- Full-pillar selector token consumed by this re-entry packet. -/
def qmStatTheoremGapReentryConsumedSelectorTokenId : String :=
  fullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditResultTokenId

/-- Result token emitted by this preparation packet. -/
def qmStatTheoremGapReentryResultTokenId : String :=
  "QM_STAT_THEOREM_GAP_REENTRY_PREPARED"

/-- Next strict target after this preparation packet. -/
def qmStatTheoremGapReentryReviewTargetId : String :=
  "review_qm_stat_theorem_gap_reentry_result"

/-- Canonical report path for this preparation packet. -/
def qmStatTheoremGapReentryReportPath : String :=
  "formal/docs/release/QM_STAT_THEOREM_GAP_REENTRY_20260510_v0.json"

/-- Focused validation target for this preparation packet. -/
def qmStatTheoremGapReentryValidationTarget : String :=
  "python -m pytest formal/python/tests/test_qm_stat_theorem_gap_reentry_gate.py -q"

/-- Selected theorem-gap item for the re-entry packet. -/
def qmStatTheoremGapReentrySelectedGapId : String :=
  "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"

/-- Category assigned to the selected theorem-gap item. -/
def qmStatTheoremGapReentrySelectedCategoryId : String :=
  "entropy_mean_variance_residual_bridge_gap"

/-- Current authority level of the selected theorem-gap item. -/
def qmStatTheoremGapReentryCurrentAuthorityLevel : String :=
  "RETAINED_SUPPLIED_TARGET_STAT_ENTROPY_STRUCTURE_REQUIRED_BY_RESIDUAL_PACKAGE"

/-- Stronger authority requested by a future bounded discharge/refutation. -/
def qmStatTheoremGapReentryIntendedStrongerAuthority : String :=
  "THEOREM_LINKED_TARGET_STAT_ENTROPY_SEMANTICS_DISCHARGE_OR_EXPLICIT_OBSTRUCTION"

/-- Retained blocker for the preparation packet nonclaim boundary. -/
def qmStatTheoremGapReentryRetainedBlockerId : String :=
  "qm_stat_theorem_gap_reentry_target_entropy_semantics_nonclaim_boundary"

/-- Candidate categories considered by the re-entry preparation packet. -/
inductive QMStatTheoremGapReentryCandidate where
  | finiteTransportResidualTheoremGap
  | entropyMeanVarianceResidualBridgeGap
  | finiteAlignmentAssumptionDischargeCandidate
  | qmStatSourceTargetMapAdmissibilityGap
  | statisticalClosureObstructionFollowup
deriving DecidableEq, Repr

/-- Stable string rendering for re-entry candidate categories. -/
def qmStatTheoremGapReentryCandidateId :
    QMStatTheoremGapReentryCandidate -> String
  | .finiteTransportResidualTheoremGap =>
      "finite_transport_residual_theorem_gap"
  | .entropyMeanVarianceResidualBridgeGap =>
      qmStatTheoremGapReentrySelectedCategoryId
  | .finiteAlignmentAssumptionDischargeCandidate =>
      "finite_alignment_assumption_discharge_candidate"
  | .qmStatSourceTargetMapAdmissibilityGap =>
      "qm_stat_source_target_map_admissibility_gap"
  | .statisticalClosureObstructionFollowup =>
      "statistical_closure_obstruction_followup"

/-- Candidate categories compared by this bounded re-entry packet. -/
def qmStatTheoremGapReentryCandidatesV0 :
    List QMStatTheoremGapReentryCandidate :=
  [ .finiteTransportResidualTheoremGap
  , .entropyMeanVarianceResidualBridgeGap
  , .finiteAlignmentAssumptionDischargeCandidate
  , .qmStatSourceTargetMapAdmissibilityGap
  , .statisticalClosureObstructionFollowup
  ]

/-- Decision emitted by the re-entry preparation packet. -/
inductive QMStatTheoremGapReentryDecision where
  | selectTargetSTATEntropySemanticsGap
  | selectFiniteTransportResidualGap
  | selectFiniteAlignmentAssumptionGap
  | selectSourceTargetMapAdmissibilityGap
  | selectStatisticalClosureObstructionFollowup
  | inferQMSTATCompletion
deriving DecidableEq, Repr

/-- Stable string rendering for re-entry decisions. -/
def qmStatTheoremGapReentryDecisionId :
    QMStatTheoremGapReentryDecision -> String
  | .selectTargetSTATEntropySemanticsGap =>
      "select_target_stat_entropy_semantics_gap"
  | .selectFiniteTransportResidualGap =>
      "select_finite_transport_residual_gap"
  | .selectFiniteAlignmentAssumptionGap =>
      "select_finite_alignment_assumption_gap"
  | .selectSourceTargetMapAdmissibilityGap =>
      "select_source_target_map_admissibility_gap"
  | .selectStatisticalClosureObstructionFollowup =>
      "select_statistical_closure_obstruction_followup"
  | .inferQMSTATCompletion => "infer_qm_stat_completion"

/-- Bounded re-entry preparation status. -/
structure QMStatTheoremGapReentryStatus where
  selector_target_consumed : Prop
  selector_target_consumed_evidence : selector_target_consumed
  selector_result_token_consumed : Prop
  selector_result_token_consumed_evidence : selector_result_token_consumed
  qm_stat_lane_selected_by_source_selector : Prop
  qm_stat_lane_selected_by_source_selector_evidence :
    qm_stat_lane_selected_by_source_selector
  source_selector_bounded_item_ready : Prop
  source_selector_bounded_item_ready_evidence :
    source_selector_bounded_item_ready
  source_probability_result_review_completed : Prop
  source_probability_result_review_completed_evidence :
    source_probability_result_review_completed
  source_probability_route_retained_as_supplied : Prop
  source_probability_route_retained_as_supplied_evidence :
    source_probability_route_retained_as_supplied
  target_entropy_semantics_currently_authorized : Prop
  target_entropy_semantics_currently_not_authorized :
    Not target_entropy_semantics_currently_authorized
  selected_decision : QMStatTheoremGapReentryDecision
  exactly_one_bounded_theorem_gap_identified : Prop
  exactly_one_bounded_theorem_gap_identified_evidence :
    exactly_one_bounded_theorem_gap_identified
  selected_gap_id : String
  selected_category : QMStatTheoremGapReentryCandidate
  selected_category_id : String
  selected_obligation_id : String
  selected_existing_blocker_id : String
  retained_blocker_id : String
  current_authority_level : String
  intended_stronger_authority : String
  candidate_categories : List QMStatTheoremGapReentryCandidate
  candidate_category_count : Nat
  selected_gap_count : Nat
  preparation_executes_gap_discharge : Prop
  preparation_does_not_execute_gap_discharge :
    Not preparation_executes_gap_discharge
  target_entropy_gap_selected : Prop
  target_entropy_gap_selected_evidence : target_entropy_gap_selected
  finite_transport_residual_gap_selected : Prop
  finite_transport_residual_gap_not_selected :
    Not finite_transport_residual_gap_selected
  finite_alignment_gap_selected : Prop
  finite_alignment_gap_not_selected : Not finite_alignment_gap_selected
  source_target_map_admissibility_gap_selected : Prop
  source_target_map_admissibility_gap_not_selected :
    Not source_target_map_admissibility_gap_selected
  statistical_closure_followup_selected : Prop
  statistical_closure_followup_not_selected :
    Not statistical_closure_followup_selected
  broader_qm_stat_theorem_work_authorized : Prop
  broader_qm_stat_theorem_work_not_authorized :
    Not broader_qm_stat_theorem_work_authorized
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
  consumed_target : String
  consumed_selector_token : String
  selected_next_target : String
  result_token : String
  selected_validation_target : String
  surface_id : String
  report_path : String
  source_selector_surface_id : String
  source_probability_result_review_surface_id : String
  residual_package_surface_id : String
  status : DerivationStatus

/--
Current re-entry preparation: select exactly the target STAT entropy semantics
theorem-gap item and rotate to result review without executing the discharge.
-/
def qmStatTheoremGapReentryStatusV0 :
    QMStatTheoremGapReentryStatus where
  selector_target_consumed := True
  selector_target_consumed_evidence := True.intro
  selector_result_token_consumed := True
  selector_result_token_consumed_evidence := True.intro
  qm_stat_lane_selected_by_source_selector :=
    fullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditStatusReadoutV0
      |>.qm_stat_theorem_gap_reentry_selected
  qm_stat_lane_selected_by_source_selector_evidence :=
    full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_qm_stat_reentry_selected_v0
  source_selector_bounded_item_ready :=
    fullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditStatusReadoutV0
      |>.bounded_theorem_gap_item_ready
  source_selector_bounded_item_ready_evidence :=
    full_pillar_target_map_next_lane_selection_after_samplerep32_axiom_audit_bounded_item_ready_v0
  source_probability_result_review_completed :=
    qmStatSourceProbabilityExtractionResultReviewStatusReadoutV0
      |>.review_completed
  source_probability_result_review_completed_evidence :=
    qm_stat_source_probability_result_review_completed_v0
  source_probability_route_retained_as_supplied :=
    qmStatSourceProbabilityExtractionResultReviewStatusReadoutV0
      |>.source_probability_retained_as_supplied
  source_probability_route_retained_as_supplied_evidence :=
    qm_stat_source_probability_result_review_retained_as_supplied_v0
  target_entropy_semantics_currently_authorized :=
    qmStatSourceProbabilityExtractionResultReviewStatusReadoutV0
      |>.target_entropy_semantics_authorized
  target_entropy_semantics_currently_not_authorized :=
    qm_stat_source_probability_result_review_target_entropy_not_authorized_v0
  selected_decision := .selectTargetSTATEntropySemanticsGap
  exactly_one_bounded_theorem_gap_identified := True
  exactly_one_bounded_theorem_gap_identified_evidence := True.intro
  selected_gap_id := qmStatTheoremGapReentrySelectedGapId
  selected_category := .entropyMeanVarianceResidualBridgeGap
  selected_category_id := qmStatTheoremGapReentrySelectedCategoryId
  selected_obligation_id :=
    qmStatTransportSemanticsEvidenceObligationId .targetEntropySemantics
  selected_existing_blocker_id :=
    phase1BlockerQMSTATTransportResidualPackageRetainedId
  retained_blocker_id := qmStatTheoremGapReentryRetainedBlockerId
  current_authority_level := qmStatTheoremGapReentryCurrentAuthorityLevel
  intended_stronger_authority :=
    qmStatTheoremGapReentryIntendedStrongerAuthority
  candidate_categories := qmStatTheoremGapReentryCandidatesV0
  candidate_category_count := qmStatTheoremGapReentryCandidatesV0.length
  selected_gap_count := 1
  preparation_executes_gap_discharge := False
  preparation_does_not_execute_gap_discharge := by
    intro h
    exact h
  target_entropy_gap_selected := True
  target_entropy_gap_selected_evidence := True.intro
  finite_transport_residual_gap_selected := False
  finite_transport_residual_gap_not_selected := by
    intro h
    exact h
  finite_alignment_gap_selected := False
  finite_alignment_gap_not_selected := by
    intro h
    exact h
  source_target_map_admissibility_gap_selected := False
  source_target_map_admissibility_gap_not_selected := by
    intro h
    exact h
  statistical_closure_followup_selected := False
  statistical_closure_followup_not_selected := by
    intro h
    exact h
  broader_qm_stat_theorem_work_authorized := False
  broader_qm_stat_theorem_work_not_authorized := by
    intro h
    exact h
  theorem_gap_discharged := False
  theorem_gap_not_discharged := by
    intro h
    exact h
  qm_stat_pillar_completion_inferred := False
  qm_stat_pillar_completion_not_inferred := by
    intro h
    exact h
  seam_closure_inferred := False
  seam_closure_not_inferred := by
    intro h
    exact h
  phase2_readiness_claim := False
  phase2_readiness_not_claimed := by
    intro h
    exact h
  empirical_adequacy_claim := False
  empirical_adequacy_not_claimed := by
    intro h
    exact h
  canonical_toe_claim := False
  canonical_toe_not_claimed := by
    intro h
    exact h
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  qft_gr_source_map_closure_authorized := False
  qft_gr_source_map_closure_not_authorized := by
    intro h
    exact h
  governance_manifest_enrollment_authorized := False
  governance_manifest_enrollment_not_authorized := by
    intro h
    exact h
  consumed_target := qmStatTheoremGapReentryConsumedTargetId
  consumed_selector_token := qmStatTheoremGapReentryConsumedSelectorTokenId
  selected_next_target := qmStatTheoremGapReentryReviewTargetId
  result_token := qmStatTheoremGapReentryResultTokenId
  selected_validation_target := qmStatTheoremGapReentryValidationTarget
  surface_id := qmStatTheoremGapReentrySurfaceId
  report_path := qmStatTheoremGapReentryReportPath
  source_selector_surface_id :=
    fullPillarTargetMapNextLaneSelectionAfterSampleRep32AxiomAuditSurfaceId
  source_probability_result_review_surface_id :=
    qmStatSourceProbabilityExtractionResultReviewSurfaceId
  residual_package_surface_id := qmStatUnifiedTransportResidualPackageSurfaceId
  status := .retained

/-- Public readout for the QM-STAT theorem-gap re-entry preparation packet. -/
def qmStatTheoremGapReentryStatusReadoutV0 :
    QMStatTheoremGapReentryStatus :=
  qmStatTheoremGapReentryStatusV0

theorem qm_stat_theorem_gap_reentry_consumes_live_target_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.consumed_target) =
      "prepare_qm_stat_theorem_gap_reentry" := by
  rfl

theorem qm_stat_theorem_gap_reentry_consumes_selector_token_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.consumed_selector_token) =
      "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_SAMPLEREP32_AXIOM_AUDIT" := by
  rfl

theorem qm_stat_theorem_gap_reentry_selector_qm_stat_lane_selected_v0 :
    qmStatTheoremGapReentryStatusReadoutV0
      |>.qm_stat_lane_selected_by_source_selector := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.qm_stat_lane_selected_by_source_selector_evidence

theorem qm_stat_theorem_gap_reentry_source_selector_bounded_item_ready_v0 :
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_selector_bounded_item_ready := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_selector_bounded_item_ready_evidence

theorem qm_stat_theorem_gap_reentry_source_probability_review_completed_v0 :
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_probability_result_review_completed := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_probability_result_review_completed_evidence

theorem qm_stat_theorem_gap_reentry_source_probability_retained_v0 :
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_probability_route_retained_as_supplied := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_probability_route_retained_as_supplied_evidence

theorem qm_stat_theorem_gap_reentry_prior_target_entropy_not_authorized_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.target_entropy_semantics_currently_authorized) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.target_entropy_semantics_currently_not_authorized

theorem qm_stat_theorem_gap_reentry_exactly_one_gap_v0 :
    qmStatTheoremGapReentryStatusReadoutV0
      |>.exactly_one_bounded_theorem_gap_identified := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.exactly_one_bounded_theorem_gap_identified_evidence

theorem qm_stat_theorem_gap_reentry_selected_gap_id_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_gap_id) =
      "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0" := by
  rfl

theorem qm_stat_theorem_gap_reentry_selected_category_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_category_id) =
      "entropy_mean_variance_residual_bridge_gap" := by
  rfl

theorem qm_stat_theorem_gap_reentry_selected_obligation_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_obligation_id) =
      "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0" := by
  rfl

theorem qm_stat_theorem_gap_reentry_selected_obligation_matches_protocol_row_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_obligation_id) =
      qmStatTransportSemanticsEvidenceObligationId .targetEntropySemantics := by
  rfl

theorem qm_stat_theorem_gap_reentry_current_authority_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.current_authority_level) =
      "RETAINED_SUPPLIED_TARGET_STAT_ENTROPY_STRUCTURE_REQUIRED_BY_RESIDUAL_PACKAGE" := by
  rfl

theorem qm_stat_theorem_gap_reentry_intended_authority_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.intended_stronger_authority) =
      "THEOREM_LINKED_TARGET_STAT_ENTROPY_SEMANTICS_DISCHARGE_OR_EXPLICIT_OBSTRUCTION" := by
  rfl

theorem qm_stat_theorem_gap_reentry_candidate_count_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.candidate_category_count) =
      5 := by
  rfl

theorem qm_stat_theorem_gap_reentry_selected_gap_count_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_gap_count) =
      1 := by
  rfl

theorem qm_stat_theorem_gap_reentry_result_token_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.result_token) =
      "QM_STAT_THEOREM_GAP_REENTRY_PREPARED" := by
  rfl

theorem qm_stat_theorem_gap_reentry_selected_next_target_v0 :
    (qmStatTheoremGapReentryStatusReadoutV0 |>.selected_next_target) =
      "review_qm_stat_theorem_gap_reentry_result" := by
  rfl

/-- The master-action frontier has advanced beyond the re-entry review handoff. -/
theorem qm_stat_theorem_gap_reentry_frontier_advanced_after_result_review_v0 :
    Option.map (fun entry => entry.next_strict_slice)
      (crossPillarFrontierEntryByRow? .masterAction) =
      some "prepare_qm_stat_target_stat_entropy_semantics_theorem_gap_bounded_attack" := by
  decide

theorem qm_stat_theorem_gap_reentry_does_not_execute_discharge_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.preparation_executes_gap_discharge) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.preparation_does_not_execute_gap_discharge

theorem qm_stat_theorem_gap_reentry_target_entropy_selected_v0 :
    qmStatTheoremGapReentryStatusReadoutV0 |>.target_entropy_gap_selected := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.target_entropy_gap_selected_evidence

theorem qm_stat_theorem_gap_reentry_finite_transport_not_selected_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.finite_transport_residual_gap_selected) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.finite_transport_residual_gap_not_selected

theorem qm_stat_theorem_gap_reentry_finite_alignment_not_selected_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.finite_alignment_gap_selected) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.finite_alignment_gap_not_selected

theorem qm_stat_theorem_gap_reentry_source_target_map_not_selected_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.source_target_map_admissibility_gap_selected) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.source_target_map_admissibility_gap_not_selected

theorem qm_stat_theorem_gap_reentry_statistical_closure_not_selected_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.statistical_closure_followup_selected) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.statistical_closure_followup_not_selected

theorem qm_stat_theorem_gap_reentry_no_broader_theorem_work_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.broader_qm_stat_theorem_work_authorized) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.broader_qm_stat_theorem_work_not_authorized

theorem qm_stat_theorem_gap_reentry_no_theorem_gap_discharge_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.theorem_gap_discharged) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.theorem_gap_not_discharged

theorem qm_stat_theorem_gap_reentry_no_qm_stat_completion_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.qm_stat_pillar_completion_inferred) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.qm_stat_pillar_completion_not_inferred

theorem qm_stat_theorem_gap_reentry_no_seam_closure_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.seam_closure_inferred) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.seam_closure_not_inferred

theorem qm_stat_theorem_gap_reentry_no_phase2_readiness_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.phase2_readiness_claim) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.phase2_readiness_not_claimed

theorem qm_stat_theorem_gap_reentry_no_empirical_adequacy_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.empirical_adequacy_claim) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.empirical_adequacy_not_claimed

theorem qm_stat_theorem_gap_reentry_no_canonical_toe_claim_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.canonical_toe_claim) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.canonical_toe_not_claimed

theorem qm_stat_theorem_gap_reentry_master_action_not_promoted_v0 :
    Not (qmStatTheoremGapReentryStatusReadoutV0 |>.master_action_promoted) := by
  exact qmStatTheoremGapReentryStatusReadoutV0 |>.master_action_not_promoted

theorem qm_stat_theorem_gap_reentry_qft_gr_not_authorized_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.qft_gr_source_map_closure_authorized) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.qft_gr_source_map_closure_not_authorized

theorem qm_stat_theorem_gap_reentry_manifest_not_enrolled_v0 :
    Not
      (qmStatTheoremGapReentryStatusReadoutV0
        |>.governance_manifest_enrollment_authorized) := by
  exact
    qmStatTheoremGapReentryStatusReadoutV0
      |>.governance_manifest_enrollment_not_authorized

end QMStatTheoremGapReentry
end Derivation
end ToeFormal
