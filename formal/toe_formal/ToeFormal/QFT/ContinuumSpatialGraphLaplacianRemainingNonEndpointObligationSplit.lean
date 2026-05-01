/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianRemainingNonEndpointObligationSplit.lean

A1A30 remaining non-endpoint obligation split after the A1A29 refined
endpoint-source assembly.

Scope:
- split the residual A2A15A1 non-endpoint evidence into five named packages
- prove those packages reconstruct the existing non-endpoint evidence object
- choose one next theorem-facing obligation instead of continuing broad splits
- make no A2A15A1, A2A15, Phase 2, or master-action promotion claim
- make no empirical claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianRemainingNonEndpointObligationSplit

open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence
open ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A30 remaining non-endpoint split. -/
def a1a30RemainingNonEndpointObligationSplitSurfaceId : String :=
  "A2A15A1A30_REMAINING_NONENDPOINT_OBLIGATION_SPLIT"

/-- Retained blocker after the A1A30 remaining non-endpoint split. -/
def phase1Blocker003A2A15A1A30RemainingNonEndpointSplitRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A30_REMAINING_NONENDPOINT_" ++
    "OBLIGATIONS_SPLIT_RETAINED"

/-- Outcome id for the bounded A1A30 split. -/
def a2a15a1RemainingNonEndpointObligationsSplitRetainedOutcomeId :
    String :=
  "A2A15A1_REMAINING_NONENDPOINT_OBLIGATIONS_SPLIT_RETAINED"

/-- Next theorem-facing scalar obligation selected after the split. -/
def a1a30NextStrictTargetId : String :=
  "attempt_raw_ibp_to_green_convergence_nonendpoint_obligation"

/-- Domain and regularity obligations that remain after the endpoint source. -/
structure RemainingNonEndpointDomainRegularityObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  analytic_interval_domain_model_supplied :
    target.analytic_interval_domain_model
  target_domain_regular_for_limit_passage_supplied :
    target.domain_regular_for_limit_passage
  contract_domain_regular_for_limit_passage_supplied :
    contract.domain_regular_for_limit_passage

/-- Raw finite IBP to continuum Green-identity convergence obligation. -/
structure RemainingNonEndpointRawIBPGreenConvergenceObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  finite_raw_ibp_green_identity_convergence_supplied :
    contract.finite_raw_ibp_to_continuum_green_identity

/-- Finite pairing to continuum pairing convergence obligation. -/
structure RemainingNonEndpointPairingConvergenceObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  finite_pairing_convergence_supplied :
    contract.finite_pairing_to_continuum_pairing

/-- Separating test-class semantics obligation. -/
structure RemainingNonEndpointSeparatingTestClassObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  separating_test_class_for_limit_supplied :
    contract.separating_test_class_for_limit

/-- Target continuum derivative/Laplacian semantics obligation. -/
structure RemainingNonEndpointTargetContinuumSemanticsObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  continuum_derivative_laplacian_semantics_supplied :
    target.continuum_derivative_laplacian_semantics

/--
The five residual non-endpoint packages reconstruct the A1A23/A1A29
non-endpoint evidence object.
-/
def nonEndpointRemainingEvidenceOfSplitObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (domainRegularity :
      RemainingNonEndpointDomainRegularityObligations contract)
    (rawIBPGreen :
      RemainingNonEndpointRawIBPGreenConvergenceObligation contract)
    (pairing :
      RemainingNonEndpointPairingConvergenceObligation contract)
    (separating :
      RemainingNonEndpointSeparatingTestClassObligation contract)
    (targetSemantics :
      RemainingNonEndpointTargetContinuumSemanticsObligation contract) :
    SpecializedA2A15A1NonEndpointRemainingEvidence contract where
  analytic_interval_domain_model_supplied :=
    domainRegularity.analytic_interval_domain_model_supplied
  continuum_derivative_laplacian_semantics_supplied :=
    targetSemantics.continuum_derivative_laplacian_semantics_supplied
  target_domain_regular_for_limit_passage_supplied :=
    domainRegularity.target_domain_regular_for_limit_passage_supplied
  finite_raw_ibp_green_identity_convergence_supplied :=
    rawIBPGreen.finite_raw_ibp_green_identity_convergence_supplied
  finite_pairing_convergence_supplied :=
    pairing.finite_pairing_convergence_supplied
  contract_domain_regular_for_limit_passage_supplied :=
    domainRegularity.contract_domain_regular_for_limit_passage_supplied
  separating_test_class_for_limit_supplied :=
    separating.separating_test_class_for_limit_supplied

/-- Project the domain/regularity package from an existing non-endpoint object. -/
def domainRegularityOfNonEndpointRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RemainingNonEndpointDomainRegularityObligations contract where
  analytic_interval_domain_model_supplied :=
    remaining.analytic_interval_domain_model_supplied
  target_domain_regular_for_limit_passage_supplied :=
    remaining.target_domain_regular_for_limit_passage_supplied
  contract_domain_regular_for_limit_passage_supplied :=
    remaining.contract_domain_regular_for_limit_passage_supplied

/-- Project the raw-IBP/Green convergence package. -/
def rawIBPGreenOfNonEndpointRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RemainingNonEndpointRawIBPGreenConvergenceObligation contract where
  finite_raw_ibp_green_identity_convergence_supplied :=
    remaining.finite_raw_ibp_green_identity_convergence_supplied

/-- Project the pairing convergence package. -/
def pairingOfNonEndpointRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RemainingNonEndpointPairingConvergenceObligation contract where
  finite_pairing_convergence_supplied :=
    remaining.finite_pairing_convergence_supplied

/-- Project the separating test-class package. -/
def separatingOfNonEndpointRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RemainingNonEndpointSeparatingTestClassObligation contract where
  separating_test_class_for_limit_supplied :=
    remaining.separating_test_class_for_limit_supplied

/-- Project the target continuum semantics package. -/
def targetSemanticsOfNonEndpointRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RemainingNonEndpointTargetContinuumSemanticsObligation contract where
  continuum_derivative_laplacian_semantics_supplied :=
    remaining.continuum_derivative_laplacian_semantics_supplied

/-- The five-way split reconstructs any existing non-endpoint package. -/
theorem remaining_nonendpoint_split_reconstructs_existing_package_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    nonEndpointRemainingEvidenceOfSplitObligations
      contract
      (domainRegularityOfNonEndpointRemainingEvidence contract remaining)
      (rawIBPGreenOfNonEndpointRemainingEvidence contract remaining)
      (pairingOfNonEndpointRemainingEvidence contract remaining)
      (separatingOfNonEndpointRemainingEvidence contract remaining)
      (targetSemanticsOfNonEndpointRemainingEvidence contract remaining) =
      remaining := by
  cases remaining
  rfl

/-- The split packages can feed the A1A29 conditional remaining constructor. -/
def specializedRemainingEvidenceOfSplitNonEndpointObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (domainRegularity :
      RemainingNonEndpointDomainRegularityObligations contract)
    (rawIBPGreen :
      RemainingNonEndpointRawIBPGreenConvergenceObligation contract)
    (pairing :
      RemainingNonEndpointPairingConvergenceObligation contract)
    (separating :
      RemainingNonEndpointSeparatingTestClassObligation contract)
    (targetSemantics :
      RemainingNonEndpointTargetContinuumSemanticsObligation contract) :
    SpecializedA2A15A1NonEndpointRemainingEvidence contract :=
  nonEndpointRemainingEvidenceOfSplitObligations
    contract domainRegularity rawIBPGreen pairing separating targetSemantics

/-- The five named obligation classes after A1A29. -/
inductive RemainingNonEndpointObligationKind where
  | domainRegularity
  | rawIBPToGreenConvergence
  | pairingConvergence
  | separatingTestClassSemantics
  | targetContinuumSemantics
deriving DecidableEq, Repr

/-- Machine-facing ids for the A1A30 obligation classes. -/
def remainingNonEndpointObligationKindId :
    RemainingNonEndpointObligationKind -> String
  | .domainRegularity =>
      "A1A30_OBLIGATION_DOMAIN_REGULARITY"
  | .rawIBPToGreenConvergence =>
      "A1A30_OBLIGATION_RAW_IBP_TO_GREEN_CONVERGENCE"
  | .pairingConvergence =>
      "A1A30_OBLIGATION_PAIRING_CONVERGENCE"
  | .separatingTestClassSemantics =>
      "A1A30_OBLIGATION_SEPARATING_TEST_CLASS_SEMANTICS"
  | .targetContinuumSemantics =>
      "A1A30_OBLIGATION_TARGET_CONTINUUM_SEMANTICS"

/-- Exact retained obligation classes after A1A29. -/
def remainingNonEndpointObligationKindsV0 :
    List RemainingNonEndpointObligationKind :=
  [ .domainRegularity
  , .rawIBPToGreenConvergence
  , .pairingConvergence
  , .separatingTestClassSemantics
  , .targetContinuumSemantics
  ]

/-- The A1A30 split has exactly five obligation classes. -/
theorem remaining_nonendpoint_obligation_kinds_length_v0 :
    remainingNonEndpointObligationKindsV0.length = 5 := by
  rfl

/-- Current A1A30 status readout. -/
structure RemainingNonEndpointObligationSplitStatus where
  obligation_split_recorded : Prop
  obligation_split_recorded_supplied : obligation_split_recorded
  reconstructs_non_endpoint_package_conditionally : Prop
  reconstructs_non_endpoint_package_conditionally_supplied :
    reconstructs_non_endpoint_package_conditionally
  endpoint_source_baseline_unchanged : Prop
  endpoint_source_baseline_unchanged_supplied :
    endpoint_source_baseline_unchanged
  non_endpoint_package_supplied : Prop
  non_endpoint_package_not_supplied : Not non_endpoint_package_supplied
  a2a15a1_witness_supplied : Prop
  a2a15a1_witness_not_supplied : Not a2a15a1_witness_supplied
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  surface_id : String
  retained_blocker_id : String
  outcome_id : String
  next_strict_target_id : String
  obligation_kind_ids : List String

/--
Current A1A30 result: the residual non-endpoint evidence has been split, and
the next scalar theorem-facing slice is the raw-IBP to Green convergence
obligation.
-/
def remainingNonEndpointObligationSplitStatusV0 :
    RemainingNonEndpointObligationSplitStatus where
  obligation_split_recorded := True
  obligation_split_recorded_supplied := True.intro
  reconstructs_non_endpoint_package_conditionally := True
  reconstructs_non_endpoint_package_conditionally_supplied := True.intro
  endpoint_source_baseline_unchanged := True
  endpoint_source_baseline_unchanged_supplied := True.intro
  non_endpoint_package_supplied := False
  non_endpoint_package_not_supplied := by
    intro h
    exact h
  a2a15a1_witness_supplied := False
  a2a15a1_witness_not_supplied := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  surface_id := a1a30RemainingNonEndpointObligationSplitSurfaceId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A30RemainingNonEndpointSplitRetainedId
  outcome_id := a2a15a1RemainingNonEndpointObligationsSplitRetainedOutcomeId
  next_strict_target_id := a1a30NextStrictTargetId
  obligation_kind_ids :=
    remainingNonEndpointObligationKindsV0.map
      remainingNonEndpointObligationKindId

/-- Short proof-facing alias for the A1A30 status. -/
def remainingNonEndpointObligationSplitStatusReadoutV0 :
    RemainingNonEndpointObligationSplitStatus :=
  remainingNonEndpointObligationSplitStatusV0

/-- A1A30 records the remaining non-endpoint split. -/
theorem remaining_nonendpoint_obligation_split_recorded_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.obligation_split_recorded := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.obligation_split_recorded_supplied

/-- A1A30 records conditional reconstruction of the non-endpoint package. -/
theorem remaining_nonendpoint_split_conditional_reconstruction_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.reconstructs_non_endpoint_package_conditionally := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.reconstructs_non_endpoint_package_conditionally_supplied

/-- A1A30 does not alter the A1A29 endpoint-source baseline. -/
theorem remaining_nonendpoint_split_endpoint_baseline_unchanged_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.endpoint_source_baseline_unchanged := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.endpoint_source_baseline_unchanged_supplied

/-- A1A30 does not supply the residual non-endpoint package. -/
theorem remaining_nonendpoint_package_not_supplied_v0 :
    Not
      (remainingNonEndpointObligationSplitStatusReadoutV0
        |>.non_endpoint_package_supplied) := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.non_endpoint_package_not_supplied

/-- A1A30 does not supply a final A2A15A1 witness. -/
theorem remaining_nonendpoint_split_a2a15a1_witness_not_supplied_v0 :
    Not
      (remainingNonEndpointObligationSplitStatusReadoutV0
        |>.a2a15a1_witness_supplied) := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.a2a15a1_witness_not_supplied

/-- Phase 2 remains unauthorized after A1A30. -/
theorem remaining_nonendpoint_split_phase2_not_authorized_v0 :
    Not
      (remainingNonEndpointObligationSplitStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.phase2_not_authorized

/-- The master action is not promoted by A1A30. -/
theorem remaining_nonendpoint_split_master_action_not_promoted_v0 :
    Not
      (remainingNonEndpointObligationSplitStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    remainingNonEndpointObligationSplitStatusReadoutV0
      |>.master_action_not_promoted

/-- The retained blocker id after A1A30 is explicit. -/
theorem remaining_nonendpoint_split_retained_blocker_id_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A30RemainingNonEndpointSplitRetainedId := by
  rfl

/-- The bounded outcome id after A1A30 is explicit. -/
theorem remaining_nonendpoint_split_outcome_id_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0.outcome_id =
      a2a15a1RemainingNonEndpointObligationsSplitRetainedOutcomeId := by
  rfl

/-- The next scalar theorem-facing obligation after A1A30 is explicit. -/
theorem remaining_nonendpoint_split_next_strict_target_v0 :
    remainingNonEndpointObligationSplitStatusReadoutV0.next_strict_target_id =
      a1a30NextStrictTargetId := by
  rfl

end

end ContinuumSpatialGraphLaplacianRemainingNonEndpointObligationSplit
end QFT
end ToeFormal
