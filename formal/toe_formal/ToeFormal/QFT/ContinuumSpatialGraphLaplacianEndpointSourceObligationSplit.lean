/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointSourceObligationSplit.lean

A1A25 endpoint-source obligation split after the A1A24 endpoint-flux evidence
derivation surface.

Scope:
- split the A1A24 concrete endpoint source into three supplied subpackages:
  representation/semantics, convergence/consistency, and orientation/trace
  compatibility
- prove that the three subpackages construct the A1A24 endpoint source
- expose the retained blocker for endpoint-source obligation discharge
- do not attempt full endpoint-flux closure, A2A15A1 closure, A2A15 closure,
  or Phase 2 authorization
- make no Phase 0-5 objective-completion claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointSourceObligationSplit

open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialEndpointFluxConvergence
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence
open ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A25 endpoint-source obligation split. -/
def a1a25EndpointSourceObligationSplitSurfaceId : String :=
  "A2A15A1A25_ENDPOINT_SOURCE_OBLIGATION_SPLIT"

/-- Retained blocker after the A1A25 endpoint-source split. -/
def phase1Blocker003A2A15A1A25EndpointSourceObligationsRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A25_ENDPOINT_SOURCE_OBLIGATIONS_" ++
    "RETAINED"

/-- Outcome id for the retained A1A25 endpoint-source obligation split. -/
def endpointSourceObligationsRetainedOutcomeId : String :=
  "ENDPOINT_SOURCE_OBLIGATIONS_RETAINED"

/--
Representation and continuum-semantics part of the A1A24 endpoint source.

This package is deliberately only a supplied package: it does not derive the
endpoint representation theorem or boundary/normal semantics.
-/
structure EndpointRepresentationSemanticsObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
  endpoint_flux_representation_supplied :
    BoundaryFluxRepresentationStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux
  continuum_boundary_trace_semantics : Prop
  continuum_boundary_trace_semantics_supplied :
    continuum_boundary_trace_semantics
  continuum_normal_derivative_semantics : Prop
  continuum_normal_derivative_semantics_supplied :
    continuum_normal_derivative_semantics
  semantics_supply_parent_boundary_trace_normal_derivative :
    continuum_boundary_trace_semantics ->
    continuum_normal_derivative_semantics ->
      target.boundary_trace_normal_derivative_semantics

/--
Convergence and finite-consistency part of the A1A24 endpoint source.

This package keeps reconstruction compatibility, convergence mode, and finite
endpoint consistency separate from the representation/semantics package.
-/
structure EndpointConvergenceConsistencyObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract) where
  boundary_reconstruction_compatibility : Prop
  boundary_reconstruction_compatibility_supplied :
    boundary_reconstruction_compatibility
  flux_term_convergence_mode : Prop
  flux_term_convergence_mode_supplied :
    flux_term_convergence_mode
  finite_endpoint_flux_consistency_theorem : Prop
  finite_endpoint_flux_consistency_theorem_supplied :
    finite_endpoint_flux_consistency_theorem
  consistency_supplies_parent_endpoint_field :
    (orientation_convention : Prop) ->
    BoundaryFluxRepresentationStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux ->
    representation.continuum_boundary_trace_semantics ->
    representation.continuum_normal_derivative_semantics ->
    orientation_convention ->
    boundary_reconstruction_compatibility ->
    flux_term_convergence_mode ->
    finite_endpoint_flux_consistency_theorem ->
      contract.finite_endpoint_flux_to_continuum_boundary_flux

/--
Orientation and trace-compatibility part of the A1A24 endpoint source.

This package isolates the orientation convention and trace-normal convergence
from the endpoint representation and finite consistency fields.
-/
structure EndpointOrientationTraceCompatibilityObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract) where
  orientation_convention : Prop
  orientation_convention_supplied :
    orientation_convention
  trace_normal_derivative_convergence_statement : Prop
  trace_normal_derivative_convergence_statement_supplied :
    trace_normal_derivative_convergence_statement
  orientation_compatibility_statement : Prop
  orientation_compatibility_statement_supplied :
    orientation_compatibility_statement
  orientation_supplies_parent_orientation :
    orientation_convention ->
      target.orientation_convention_for_limit
  trace_source_supplies_parent_trace_normal_convergence :
    trace_normal_derivative_convergence_statement ->
    representation.continuum_normal_derivative_semantics ->
      contract.trace_normal_derivative_convergence
  orientation_source_supplies_parent_orientation_compatibility :
    orientation_compatibility_statement ->
    orientation_convention ->
      contract.orientation_convention_compatible

/--
The three A1A25 subpackages reconstruct the A1A24 concrete endpoint source.
-/
def specializedEndpointFluxEvidenceSourceOfSplitObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (convergence :
      EndpointConvergenceConsistencyObligations contract representation)
    (orientation :
      EndpointOrientationTraceCompatibilityObligations
        contract representation) :
    SpecializedEndpointFluxEvidenceSource contract where
  endpoint_flux_representation_supplied :=
    representation.endpoint_flux_representation_supplied
  continuum_boundary_trace_semantics :=
    representation.continuum_boundary_trace_semantics
  continuum_boundary_trace_semantics_supplied :=
    representation.continuum_boundary_trace_semantics_supplied
  continuum_normal_derivative_semantics :=
    representation.continuum_normal_derivative_semantics
  continuum_normal_derivative_semantics_supplied :=
    representation.continuum_normal_derivative_semantics_supplied
  orientation_convention :=
    orientation.orientation_convention
  orientation_convention_supplied :=
    orientation.orientation_convention_supplied
  boundary_reconstruction_compatibility :=
    convergence.boundary_reconstruction_compatibility
  boundary_reconstruction_compatibility_supplied :=
    convergence.boundary_reconstruction_compatibility_supplied
  flux_term_convergence_mode :=
    convergence.flux_term_convergence_mode
  flux_term_convergence_mode_supplied :=
    convergence.flux_term_convergence_mode_supplied
  finite_endpoint_flux_consistency_theorem :=
    convergence.finite_endpoint_flux_consistency_theorem
  finite_endpoint_flux_consistency_theorem_supplied :=
    convergence.finite_endpoint_flux_consistency_theorem_supplied
  trace_normal_derivative_convergence_statement :=
    orientation.trace_normal_derivative_convergence_statement
  trace_normal_derivative_convergence_statement_supplied :=
    orientation.trace_normal_derivative_convergence_statement_supplied
  orientation_compatibility_statement :=
    orientation.orientation_compatibility_statement
  orientation_compatibility_statement_supplied :=
    orientation.orientation_compatibility_statement_supplied
  semantics_supply_parent_boundary_trace_normal_derivative :=
    representation.semantics_supply_parent_boundary_trace_normal_derivative
  orientation_supplies_parent_orientation :=
    orientation.orientation_supplies_parent_orientation
  consistency_supplies_parent_endpoint_field := by
    intro hRep hBoundary hNormal hOrientation hReconstruct hMode hConsistency
    exact
      convergence.consistency_supplies_parent_endpoint_field
        orientation.orientation_convention
        hRep hBoundary hNormal hOrientation hReconstruct hMode hConsistency
  trace_source_supplies_parent_trace_normal_convergence := by
    intro hTrace hNormal
    exact
      orientation.trace_source_supplies_parent_trace_normal_convergence
        hTrace hNormal
  orientation_source_supplies_parent_orientation_compatibility := by
    intro hCompat hOrientation
    exact
      orientation.orientation_source_supplies_parent_orientation_compatibility
        hCompat hOrientation

/-- The three supplied subpackages construct a concrete endpoint source. -/
theorem endpoint_source_split_obligations_construct_source_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (convergence :
      EndpointConvergenceConsistencyObligations contract representation)
    (orientation :
      EndpointOrientationTraceCompatibilityObligations
        contract representation) :
    Nonempty (SpecializedEndpointFluxEvidenceSource contract) := by
  exact
    ⟨specializedEndpointFluxEvidenceSourceOfSplitObligations
      contract representation convergence orientation⟩

/-- The split source supplies the A1A23 channel evidence package. -/
def endpointFluxChannelEvidenceOfSplitObligations
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (convergence :
      EndpointConvergenceConsistencyObligations contract representation)
    (orientation :
      EndpointOrientationTraceCompatibilityObligations
        contract representation) :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) :=
  endpointFluxChannelEvidenceOfSpecializedSource
    contract
    (specializedEndpointFluxEvidenceSourceOfSplitObligations
      contract representation convergence orientation)

/-- The split source conditionally supplies the specialized endpoint field. -/
theorem endpoint_source_split_obligations_supply_endpoint_field_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (convergence :
      EndpointConvergenceConsistencyObligations contract representation)
    (orientation :
      EndpointOrientationTraceCompatibilityObligations
        contract representation) :
    contract.finite_endpoint_flux_to_continuum_boundary_flux := by
  exact
    specialized_endpoint_flux_evidence_supplies_endpoint_field_v0
      contract
      (endpointFluxChannelEvidenceOfSplitObligations
        contract representation convergence orientation)

/-- Remaining objects after the A1A25 endpoint-source split. -/
inductive EndpointSourceObligationSplitObstruction where
  | noRepresentationSemanticsPackage
  | noConvergenceConsistencyPackage
  | noOrientationTraceCompatibilityPackage
  | noRemainingNonEndpointA2A15A1Evidence
  | noA2A15A1FinalWitness
  | noA2A15BoundaryFluxParent
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A25 objects. -/
def endpointSourceObligationSplitObstructionId :
    EndpointSourceObligationSplitObstruction -> String
  | .noRepresentationSemanticsPackage =>
      "a1a25_obstruction_no_representation_semantics_package"
  | .noConvergenceConsistencyPackage =>
      "a1a25_obstruction_no_convergence_consistency_package"
  | .noOrientationTraceCompatibilityPackage =>
      "a1a25_obstruction_no_orientation_trace_compatibility_package"
  | .noRemainingNonEndpointA2A15A1Evidence =>
      "a1a25_obstruction_no_remaining_non_endpoint_a2a15a1_evidence"
  | .noA2A15A1FinalWitness =>
      "a1a25_obstruction_no_a2a15a1_final_witness"
  | .noA2A15BoundaryFluxParent =>
      "a1a25_obstruction_no_a2a15_boundary_flux_parent"
  | .noPhase2Authorization =>
      "a1a25_obstruction_no_phase2_authorization"

/-- Exact obstruction list after the A1A25 split. -/
def endpointSourceObligationSplitObstructionsV0 :
    List EndpointSourceObligationSplitObstruction :=
  [ .noRepresentationSemanticsPackage
  , .noConvergenceConsistencyPackage
  , .noOrientationTraceCompatibilityPackage
  , .noRemainingNonEndpointA2A15A1Evidence
  , .noA2A15A1FinalWitness
  , .noA2A15BoundaryFluxParent
  , .noPhase2Authorization
  ]

/-- The A1A25 obstruction list is stable and explicit. -/
theorem endpoint_source_obligation_split_obstructions_v0_expected :
    endpointSourceObligationSplitObstructionsV0 =
      [ .noRepresentationSemanticsPackage
      , .noConvergenceConsistencyPackage
      , .noOrientationTraceCompatibilityPackage
      , .noRemainingNonEndpointA2A15A1Evidence
      , .noA2A15A1FinalWitness
      , .noA2A15BoundaryFluxParent
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A25 records a split and conditional source constructor. -/
def endpointSourceObligationSplitSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A25 successor kind is stable and explicit. -/
theorem endpoint_source_obligation_split_successor_kinds_v0_expected :
    endpointSourceObligationSplitSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A25 endpoint-source split. -/
structure EndpointSourceObligationSplitStatus where
  representation_semantics_package_defined : Prop
  representation_semantics_package_defined_supplied :
    representation_semantics_package_defined
  convergence_consistency_package_defined : Prop
  convergence_consistency_package_defined_supplied :
    convergence_consistency_package_defined
  orientation_trace_package_defined : Prop
  orientation_trace_package_defined_supplied :
    orientation_trace_package_defined
  split_packages_construct_source : Prop
  split_packages_construct_source_supplied :
    split_packages_construct_source
  endpoint_source_derivation_supplied : Prop
  endpoint_source_derivation_not_supplied :
    Not endpoint_source_derivation_supplied
  remaining_non_endpoint_evidence_supplied : Prop
  remaining_non_endpoint_evidence_not_supplied :
    Not remaining_non_endpoint_evidence_supplied
  a2a15a1_final_witness_supplied : Prop
  a2a15a1_final_witness_not_supplied :
    Not a2a15a1_final_witness_supplied
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  surface_id : String
  prior_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String

/--
Current A1A25 result: the endpoint source is decomposed into three supplied
subpackages, but none of those packages is derived here.
-/
def endpointSourceObligationSplitStatusV0 :
    EndpointSourceObligationSplitStatus where
  representation_semantics_package_defined := True
  representation_semantics_package_defined_supplied := True.intro
  convergence_consistency_package_defined := True
  convergence_consistency_package_defined_supplied := True.intro
  orientation_trace_package_defined := True
  orientation_trace_package_defined_supplied := True.intro
  split_packages_construct_source := True
  split_packages_construct_source_supplied := True.intro
  endpoint_source_derivation_supplied := False
  endpoint_source_derivation_not_supplied := by
    intro h
    exact h
  remaining_non_endpoint_evidence_supplied := False
  remaining_non_endpoint_evidence_not_supplied := by
    intro h
    exact h
  a2a15a1_final_witness_supplied := False
  a2a15a1_final_witness_not_supplied := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := a1a25EndpointSourceObligationSplitSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A24EndpointFluxEvidenceDerivationRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A25EndpointSourceObligationsRetainedId
  outcome_id := endpointSourceObligationsRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointSourceObligationSplitSuccessorKindsV0
  obstruction_ids :=
    endpointSourceObligationSplitObstructionsV0.map
      endpointSourceObligationSplitObstructionId

/-- Short proof-facing status alias. -/
def endpointSourceObligationSplitStatusReadoutV0 :
    EndpointSourceObligationSplitStatus :=
  endpointSourceObligationSplitStatusV0

/-- The representation/semantics package is defined. -/
theorem endpoint_source_representation_package_defined_v0 :
    endpointSourceObligationSplitStatusReadoutV0
      |>.representation_semantics_package_defined := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.representation_semantics_package_defined_supplied

/-- The convergence/consistency package is defined. -/
theorem endpoint_source_convergence_package_defined_v0 :
    endpointSourceObligationSplitStatusReadoutV0
      |>.convergence_consistency_package_defined := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.convergence_consistency_package_defined_supplied

/-- The orientation/trace package is defined. -/
theorem endpoint_source_orientation_trace_package_defined_v0 :
    endpointSourceObligationSplitStatusReadoutV0
      |>.orientation_trace_package_defined := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.orientation_trace_package_defined_supplied

/-- A1A25 records the conditional package-to-source constructor. -/
theorem endpoint_source_split_constructor_defined_status_v0 :
    endpointSourceObligationSplitStatusReadoutV0
      |>.split_packages_construct_source := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.split_packages_construct_source_supplied

/-- The endpoint-source derivation is not supplied by A1A25. -/
theorem endpoint_source_obligation_split_source_not_supplied_v0 :
    Not
      (endpointSourceObligationSplitStatusReadoutV0
        |>.endpoint_source_derivation_supplied) := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.endpoint_source_derivation_not_supplied

/-- Non-endpoint remaining evidence is not supplied by A1A25. -/
theorem endpoint_source_obligation_split_non_endpoint_not_supplied_v0 :
    Not
      (endpointSourceObligationSplitStatusReadoutV0
        |>.remaining_non_endpoint_evidence_supplied) := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.remaining_non_endpoint_evidence_not_supplied

/-- A1A25 does not supply a final A2A15A1 witness. -/
theorem endpoint_source_obligation_split_final_witness_not_supplied_v0 :
    Not
      (endpointSourceObligationSplitStatusReadoutV0
        |>.a2a15a1_final_witness_supplied) := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.a2a15a1_final_witness_not_supplied

/-- Phase 2 remains unauthorized after A1A25. -/
theorem endpoint_source_obligation_split_phase2_not_authorized_v0 :
    Not
      (endpointSourceObligationSplitStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    endpointSourceObligationSplitStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A25 retained blocker id is exposed. -/
theorem endpoint_source_obligation_split_retained_id_v0 :
    endpointSourceObligationSplitStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A25EndpointSourceObligationsRetainedId := by
  rfl

/-- The A1A25 outcome id is exposed. -/
theorem endpoint_source_obligation_split_outcome_id_v0 :
    endpointSourceObligationSplitStatusReadoutV0.outcome_id =
      endpointSourceObligationsRetainedOutcomeId := by
  rfl

/-- The A1A25 obstruction ids are exposed. -/
theorem endpoint_source_obligation_split_obstruction_ids_v0 :
    endpointSourceObligationSplitStatusReadoutV0.obstruction_ids =
      endpointSourceObligationSplitObstructionsV0.map
        endpointSourceObligationSplitObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianEndpointSourceObligationSplit
end QFT
end ToeFormal
