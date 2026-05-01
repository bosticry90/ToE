/-
ToeFormal/QFT/ContinuumSpatialGraphLaplianRefinedEndpointSourceAssembly.lean

A1A29 refined endpoint-source assembly after the A1A26-A1A28 endpoint
subpackage refinements.

Scope:
- check whether the A1A26 representation/semantics package, A1A27
  convergence/consistency package, and A1A28 orientation/trace package fit
  the A1A25 endpoint-source constructor
- prove the refined supplied pieces assemble the endpoint-flux evidence source
- expose the remaining non-endpoint A2A15A1 obligations
- make no A2A15A1, A2A15, Phase 2, or master-action promotion claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialEndpointFluxConvergence
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness
open ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence
open ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation
open ContinuumSpatialGraphLaplacianEndpointSourceObligationSplit
open ContinuumSpatialGraphLaplacianEndpointRepresentationSemanticsObligation
open ContinuumSpatialGraphLaplacianEndpointConvergenceConsistencyObligation
open ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A29 refined endpoint-source assembly. -/
def a1a29RefinedEndpointSourceAssemblySurfaceId : String :=
  "A2A15A1A29_REFINED_ENDPOINT_SOURCE_ASSEMBLY"

/-- Retained blocker after the A1A29 refined endpoint-source assembly. -/
def phase1Blocker003A2A15A1A29RemainingNonEndpointObligationsRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A29_REMAINING_NONENDPOINT_" ++
    "OBLIGATIONS_RETAINED"

/-- Outcome id for the positive A1A29 assembly result. -/
def refinedEndpointSourceAssembledOutcomeId : String :=
  "REFINED_ENDPOINT_SOURCE_ASSEMBLED_A2A15A1_REMAINING_NONENDPOINT_" ++
    "OBLIGATIONS_RETAINED"

/-- Outcome id for the not-reached A1A29 interface-mismatch branch. -/
def refinedEndpointSourceAssemblyInterfaceMismatchOutcomeId : String :=
  "REFINED_ENDPOINT_SOURCE_ASSEMBLY_RETAINED_INTERFACE_MISMATCH"

/-- A1A26 supplied pieces as the common representation package for A1A29. -/
def refinedEndpointRepresentationPackageOfA1A26
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics) :
    EndpointRepresentationSemanticsObligations contract :=
  endpointRepresentationSemanticsObligationsOfSuppliedPieces
    contract representation semantics representationBridge

/--
A1A27 supplied pieces, parameterized over the A1A26 representation package,
as the common convergence/consistency package for A1A29.
-/
def refinedEndpointConvergencePackageOfA1A27
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representationPackage :
      EndpointRepresentationSemanticsObligations contract)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract representationPackage)
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract representationPackage)
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract representationPackage)
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract representationPackage reconstruction mode consistency) :
    EndpointConvergenceConsistencyObligations
      contract representationPackage :=
  endpointConvergenceConsistencyObligationsOfSuppliedPieces
    contract representationPackage reconstruction mode consistency
    convergenceBridge

/--
A1A28 supplied pieces, parameterized over the A1A26 representation package,
as the common orientation/trace package for A1A29.
-/
def refinedEndpointOrientationTracePackageOfA1A28
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representationPackage :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation
        contract representationPackage)
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract representationPackage)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representationPackage)
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract representationPackage orientation trace compatibility) :
    EndpointOrientationTraceCompatibilityObligations
      contract representationPackage :=
  endpointOrientationTraceCompatibilityObligationsOfSuppliedPieces
    contract representationPackage orientation trace compatibility
    orientationBridge

/--
The refined A1A26, A1A27, and A1A28 supplied pieces assemble into the A1A24
concrete endpoint-flux evidence source through the A1A25 constructor.
-/
def refinedEndpointSourceOfA1A26A1A27A1A28
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility) :
    SpecializedEndpointFluxEvidenceSource contract :=
  let representationPackage :=
    refinedEndpointRepresentationPackageOfA1A26
      contract representation semantics representationBridge
  let convergencePackage :=
    refinedEndpointConvergencePackageOfA1A27
      contract representationPackage reconstruction mode consistency
      convergenceBridge
  let orientationPackage :=
    refinedEndpointOrientationTracePackageOfA1A28
      contract representationPackage orientation trace compatibility
      orientationBridge
  specializedEndpointFluxEvidenceSourceOfSplitObligations
    contract representationPackage convergencePackage orientationPackage

/-- A1A26-A1A28 supplied pieces assemble a concrete endpoint source. -/
theorem refined_endpoint_source_assembled_from_a1a26_a1a27_a1a28_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility) :
    Nonempty (SpecializedEndpointFluxEvidenceSource contract) := by
  exact
    ⟨refinedEndpointSourceOfA1A26A1A27A1A28
      contract representation semantics representationBridge reconstruction
      mode consistency convergenceBridge orientation trace compatibility
      orientationBridge⟩

/-- The refined endpoint source supplies the endpoint-flux channel evidence. -/
def refinedEndpointFluxChannelEvidenceOfA1A26A1A27A1A28
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility) :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) :=
  endpointFluxChannelEvidenceOfSpecializedSource
    contract
    (refinedEndpointSourceOfA1A26A1A27A1A28
      contract representation semantics representationBridge reconstruction
      mode consistency convergenceBridge orientation trace compatibility
      orientationBridge)

/-- The refined endpoint source supplies the specialized endpoint field. -/
theorem refined_endpoint_source_supplies_endpoint_field_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility) :
    contract.finite_endpoint_flux_to_continuum_boundary_flux := by
  exact
    specialized_endpoint_flux_evidence_supplies_endpoint_field_v0
      contract
      (refinedEndpointFluxChannelEvidenceOfA1A26A1A27A1A28
        contract representation semantics representationBridge reconstruction
        mode consistency convergenceBridge orientation trace compatibility
        orientationBridge)

/--
With separately supplied non-endpoint evidence, the refined endpoint source
builds the full remaining-evidence package. The non-endpoint evidence is not
constructed by A1A29.
-/
def specializedRemainingEvidenceOfRefinedEndpointSource
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    SpecializedA2A15A1RemainingEvidence contract :=
  specializedRemainingEvidenceOfEndpointFluxSource
    contract
    (refinedEndpointSourceOfA1A26A1A27A1A28
      contract representation semantics representationBridge reconstruction
      mode consistency convergenceBridge orientation trace compatibility
      orientationBridge)
    remaining

/--
With separately supplied non-endpoint evidence, the refined endpoint source
feeds the conditional specialized A2A15A1 witness.  A1A29 does not supply that
non-endpoint evidence.
-/
def specializedA2A15A1WitnessOfRefinedEndpointSource
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointFluxRepresentationTheoremObligation contract)
    (semantics :
      EndpointTraceNormalSemanticsObligation contract)
    (representationBridge :
      EndpointRepresentationSemanticsParentBridge contract semantics)
    (reconstruction :
      EndpointBoundaryReconstructionCompatibilityObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (mode :
      EndpointFluxTermConvergenceModeObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (consistency :
      EndpointFiniteFluxConsistencyTheoremObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (convergenceBridge :
      EndpointConvergenceConsistencyParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        reconstruction mode consistency)
    (orientation :
      EndpointOrientationConventionObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (trace :
      EndpointTraceNormalConvergenceObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge))
    (orientationBridge :
      EndpointOrientationTraceParentBridge
        contract
        (refinedEndpointRepresentationPackageOfA1A26
          contract representation semantics representationBridge)
        orientation trace compatibility)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    AnalyticIntervalLiftWitness
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) :=
  specializedA2A15A1WitnessOfEndpointFluxSource
    contract
    (refinedEndpointSourceOfA1A26A1A27A1A28
      contract representation semantics representationBridge reconstruction
      mode consistency convergenceBridge orientation trace compatibility
      orientationBridge)
    remaining

/-- Remaining objects after the A1A29 refined endpoint-source assembly. -/
inductive RefinedEndpointSourceAssemblyObstruction where
  | noRemainingNonEndpointA2A15A1Evidence
  | noAnalyticIntervalDomainModel
  | noContinuumDerivativeLaplacianSemantics
  | noTargetDomainRegularityForLimitPassage
  | noFiniteRawIBPGreenIdentityConvergence
  | noFinitePairingConvergence
  | noContractDomainRegularityForLimitPassage
  | noSeparatingTestClassForLimit
  | noA2A15A1FinalWitness
  | noA2A15BoundaryFluxParent
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A29 objects. -/
def refinedEndpointSourceAssemblyObstructionId :
    RefinedEndpointSourceAssemblyObstruction -> String
  | .noRemainingNonEndpointA2A15A1Evidence =>
      "a1a29_obstruction_no_remaining_non_endpoint_a2a15a1_evidence"
  | .noAnalyticIntervalDomainModel =>
      "a1a29_obstruction_no_analytic_interval_domain_model"
  | .noContinuumDerivativeLaplacianSemantics =>
      "a1a29_obstruction_no_continuum_derivative_laplacian_semantics"
  | .noTargetDomainRegularityForLimitPassage =>
      "a1a29_obstruction_no_target_domain_regularity_for_limit_passage"
  | .noFiniteRawIBPGreenIdentityConvergence =>
      "a1a29_obstruction_no_finite_raw_ibp_green_identity_convergence"
  | .noFinitePairingConvergence =>
      "a1a29_obstruction_no_finite_pairing_convergence"
  | .noContractDomainRegularityForLimitPassage =>
      "a1a29_obstruction_no_contract_domain_regularity_for_limit_passage"
  | .noSeparatingTestClassForLimit =>
      "a1a29_obstruction_no_separating_test_class_for_limit"
  | .noA2A15A1FinalWitness =>
      "a1a29_obstruction_no_a2a15a1_final_witness"
  | .noA2A15BoundaryFluxParent =>
      "a1a29_obstruction_no_a2a15_boundary_flux_parent"
  | .noPhase2Authorization =>
      "a1a29_obstruction_no_phase2_authorization"

/-- Exact obstruction list after A1A29. -/
def refinedEndpointSourceAssemblyObstructionsV0 :
    List RefinedEndpointSourceAssemblyObstruction :=
  [ .noRemainingNonEndpointA2A15A1Evidence
  , .noAnalyticIntervalDomainModel
  , .noContinuumDerivativeLaplacianSemantics
  , .noTargetDomainRegularityForLimitPassage
  , .noFiniteRawIBPGreenIdentityConvergence
  , .noFinitePairingConvergence
  , .noContractDomainRegularityForLimitPassage
  , .noSeparatingTestClassForLimit
  , .noA2A15A1FinalWitness
  , .noA2A15BoundaryFluxParent
  , .noPhase2Authorization
  ]

/-- The A1A29 obstruction list is stable and explicit. -/
theorem refined_endpoint_source_assembly_obstructions_v0_expected :
    refinedEndpointSourceAssemblyObstructionsV0 =
      [ .noRemainingNonEndpointA2A15A1Evidence
      , .noAnalyticIntervalDomainModel
      , .noContinuumDerivativeLaplacianSemantics
      , .noTargetDomainRegularityForLimitPassage
      , .noFiniteRawIBPGreenIdentityConvergence
      , .noFinitePairingConvergence
      , .noContractDomainRegularityForLimitPassage
      , .noSeparatingTestClassForLimit
      , .noA2A15A1FinalWitness
      , .noA2A15BoundaryFluxParent
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A29 assembles the endpoint source and records the remaining obstruction. -/
def refinedEndpointSourceAssemblySuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A29 successor kind is stable and explicit. -/
theorem refined_endpoint_source_assembly_successor_kinds_v0_expected :
    refinedEndpointSourceAssemblySuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A29 refined endpoint-source assembly. -/
structure RefinedEndpointSourceAssemblyStatus where
  refined_endpoint_source_assembled : Prop
  refined_endpoint_source_assembled_supplied :
    refined_endpoint_source_assembled
  interface_mismatch_detected : Prop
  interface_mismatch_not_detected :
    Not interface_mismatch_detected
  endpoint_channel_evidence_available : Prop
  endpoint_channel_evidence_available_supplied :
    endpoint_channel_evidence_available
  endpoint_field_supplied : Prop
  endpoint_field_supplied_witness : endpoint_field_supplied
  conditional_remaining_evidence_constructor_defined : Prop
  conditional_remaining_evidence_constructor_defined_supplied :
    conditional_remaining_evidence_constructor_defined
  remaining_non_endpoint_evidence_supplied : Prop
  remaining_non_endpoint_evidence_not_supplied :
    Not remaining_non_endpoint_evidence_supplied
  a2a15a1_final_witness_supplied : Prop
  a2a15a1_final_witness_not_supplied :
    Not a2a15a1_final_witness_supplied
  a2a15_parent_supplied : Prop
  a2a15_parent_not_supplied : Not a2a15_parent_supplied
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  surface_id : String
  prior_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  blocked_outcome_not_reached_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String

/--
Current A1A29 result: the refined endpoint-source assembly succeeds, while the
non-endpoint A2A15A1 obligations remain independent and retained.
-/
def refinedEndpointSourceAssemblyStatusV0 :
    RefinedEndpointSourceAssemblyStatus where
  refined_endpoint_source_assembled := True
  refined_endpoint_source_assembled_supplied := True.intro
  interface_mismatch_detected := False
  interface_mismatch_not_detected := by
    intro h
    exact h
  endpoint_channel_evidence_available := True
  endpoint_channel_evidence_available_supplied := True.intro
  endpoint_field_supplied := True
  endpoint_field_supplied_witness := True.intro
  conditional_remaining_evidence_constructor_defined := True
  conditional_remaining_evidence_constructor_defined_supplied := True.intro
  remaining_non_endpoint_evidence_supplied := False
  remaining_non_endpoint_evidence_not_supplied := by
    intro h
    exact h
  a2a15a1_final_witness_supplied := False
  a2a15a1_final_witness_not_supplied := by
    intro h
    exact h
  a2a15_parent_supplied := False
  a2a15_parent_not_supplied := by
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
  surface_id := a1a29RefinedEndpointSourceAssemblySurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A28EndpointOrientationTraceCompatibilityRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A29RemainingNonEndpointObligationsRetainedId
  outcome_id := refinedEndpointSourceAssembledOutcomeId
  blocked_outcome_not_reached_id :=
    refinedEndpointSourceAssemblyInterfaceMismatchOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := refinedEndpointSourceAssemblySuccessorKindsV0
  obstruction_ids :=
    refinedEndpointSourceAssemblyObstructionsV0.map
      refinedEndpointSourceAssemblyObstructionId

/-- Short proof-facing status alias. -/
def refinedEndpointSourceAssemblyStatusReadoutV0 :
    RefinedEndpointSourceAssemblyStatus :=
  refinedEndpointSourceAssemblyStatusV0

/-- A1A29 records that the refined endpoint source assembles. -/
theorem refined_endpoint_source_assembly_status_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.refined_endpoint_source_assembled := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.refined_endpoint_source_assembled_supplied

/-- A1A29 records that the interface-mismatch branch is not reached. -/
theorem refined_endpoint_source_interface_mismatch_not_detected_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.interface_mismatch_detected) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.interface_mismatch_not_detected

/-- A1A29 records endpoint channel evidence availability. -/
theorem refined_endpoint_source_channel_evidence_available_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.endpoint_channel_evidence_available := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.endpoint_channel_evidence_available_supplied

/-- A1A29 records endpoint-field routing from the refined endpoint source. -/
theorem refined_endpoint_source_endpoint_field_status_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.endpoint_field_supplied := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.endpoint_field_supplied_witness

/-- A1A29 records the conditional remaining-evidence constructor. -/
theorem refined_endpoint_source_remaining_constructor_status_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.conditional_remaining_evidence_constructor_defined := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.conditional_remaining_evidence_constructor_defined_supplied

/-- Non-endpoint A2A15A1 evidence is not supplied by A1A29. -/
theorem refined_endpoint_source_non_endpoint_not_supplied_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.remaining_non_endpoint_evidence_supplied) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.remaining_non_endpoint_evidence_not_supplied

/-- A1A29 does not supply a final A2A15A1 witness. -/
theorem refined_endpoint_source_final_witness_not_supplied_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.a2a15a1_final_witness_supplied) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.a2a15a1_final_witness_not_supplied

/-- A1A29 does not supply the parent A2A15 boundary-flux route. -/
theorem refined_endpoint_source_a2a15_parent_not_supplied_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.a2a15_parent_supplied) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.a2a15_parent_not_supplied

/-- Phase 2 remains unauthorized after A1A29. -/
theorem refined_endpoint_source_phase2_not_authorized_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.phase2_not_authorized

/-- The master action is not promoted by A1A29. -/
theorem refined_endpoint_source_master_action_not_promoted_v0 :
    Not
      (refinedEndpointSourceAssemblyStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    refinedEndpointSourceAssemblyStatusReadoutV0
      |>.master_action_not_promoted

/-- The A1A29 retained blocker id is exposed. -/
theorem refined_endpoint_source_assembly_retained_id_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A29RemainingNonEndpointObligationsRetainedId := by
  rfl

/-- The A1A29 positive outcome id is exposed. -/
theorem refined_endpoint_source_assembly_outcome_id_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0.outcome_id =
      refinedEndpointSourceAssembledOutcomeId := by
  rfl

/-- The A1A29 interface-mismatch branch is explicitly not reached. -/
theorem refined_endpoint_source_mismatch_outcome_not_reached_v0 :
    (refinedEndpointSourceAssemblyStatusReadoutV0
      |>.blocked_outcome_not_reached_id) =
        refinedEndpointSourceAssemblyInterfaceMismatchOutcomeId := by
  rfl

/-- The A1A29 obstruction ids are exposed. -/
theorem refined_endpoint_source_assembly_obstruction_ids_v0 :
    refinedEndpointSourceAssemblyStatusReadoutV0.obstruction_ids =
      refinedEndpointSourceAssemblyObstructionsV0.map
        refinedEndpointSourceAssemblyObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly
end QFT
end ToeFormal
