/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation.lean

A1A24 endpoint-flux evidence derivation attempt for the specialized A2A15A1
witness route.

Scope:
- define the concrete source shape that would derive the A2A15A1B
  endpoint-flux evidence package
- state the required endpoint representation, boundary trace/normal semantics,
  trace-normal convergence, orientation compatibility, reconstruction
  compatibility, flux-convergence mode, and finite endpoint consistency theorem
- prove that such a source builds the A1A23 supplied endpoint-flux channel
  evidence package
- prove that the resulting endpoint package feeds the specialized A1A22
  remaining-evidence package when the non-endpoint obligations are supplied
- retain derivation of the source itself, A2A15A1 closure, A2A15 closure, and
  Phase 2 authorization
- make no Phase 0-5 objective-completion claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialEndpointFluxConvergence
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness
open ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A24 endpoint-flux evidence derivation attempt. -/
def a1a24EndpointFluxEvidenceDerivationSurfaceId : String :=
  "A2A15A1A24_ENDPOINT_FLUX_EVIDENCE_DERIVATION"

/-- Retained blocker after the A1A24 endpoint-flux derivation attempt. -/
def phase1Blocker003A2A15A1A24EndpointFluxEvidenceDerivationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A24_ENDPOINT_FLUX_EVIDENCE_" ++
    "DERIVATION_RETAINED"

/-- Outcome id for the retained A1A24 endpoint-flux derivation slice. -/
def endpointFluxEvidenceDerivationRetainedOutcomeId : String :=
  "ENDPOINT_FLUX_EVIDENCE_DERIVATION_RETAINED"

/--
Concrete endpoint-flux source shape for the specialized parent contract.

This is the evidence source whose derivation would close the A1A23 endpoint
slot.  It intentionally records the analytic obligations separately from the
remaining non-endpoint A2A15A1 fields.
-/
structure SpecializedEndpointFluxEvidenceSource
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
  orientation_convention : Prop
  orientation_convention_supplied :
    orientation_convention
  boundary_reconstruction_compatibility : Prop
  boundary_reconstruction_compatibility_supplied :
    boundary_reconstruction_compatibility
  flux_term_convergence_mode : Prop
  flux_term_convergence_mode_supplied :
    flux_term_convergence_mode
  finite_endpoint_flux_consistency_theorem : Prop
  finite_endpoint_flux_consistency_theorem_supplied :
    finite_endpoint_flux_consistency_theorem
  trace_normal_derivative_convergence_statement : Prop
  trace_normal_derivative_convergence_statement_supplied :
    trace_normal_derivative_convergence_statement
  orientation_compatibility_statement : Prop
  orientation_compatibility_statement_supplied :
    orientation_compatibility_statement
  semantics_supply_parent_boundary_trace_normal_derivative :
    continuum_boundary_trace_semantics ->
    continuum_normal_derivative_semantics ->
      target.boundary_trace_normal_derivative_semantics
  orientation_supplies_parent_orientation :
    orientation_convention ->
      target.orientation_convention_for_limit
  consistency_supplies_parent_endpoint_field :
    BoundaryFluxRepresentationStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux ->
    continuum_boundary_trace_semantics ->
    continuum_normal_derivative_semantics ->
    orientation_convention ->
    boundary_reconstruction_compatibility ->
    flux_term_convergence_mode ->
    finite_endpoint_flux_consistency_theorem ->
      contract.finite_endpoint_flux_to_continuum_boundary_flux
  trace_source_supplies_parent_trace_normal_convergence :
    trace_normal_derivative_convergence_statement ->
    continuum_normal_derivative_semantics ->
      contract.trace_normal_derivative_convergence
  orientation_source_supplies_parent_orientation_compatibility :
    orientation_compatibility_statement ->
    orientation_convention ->
      contract.orientation_convention_compatible

/--
A concrete endpoint-flux source builds the A2A15A1B channel evidence package
expected by A1A23.
-/
def endpointFluxChannelEvidenceOfSpecializedSource
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract) :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) where
  endpoint_flux_representation :=
    BoundaryFluxRepresentationStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux
  endpoint_flux_representation_supplied :=
    source.endpoint_flux_representation_supplied
  continuum_boundary_trace_semantics :=
    source.continuum_boundary_trace_semantics
  continuum_boundary_trace_semantics_supplied :=
    source.continuum_boundary_trace_semantics_supplied
  continuum_normal_derivative_semantics :=
    source.continuum_normal_derivative_semantics
  continuum_normal_derivative_semantics_supplied :=
    source.continuum_normal_derivative_semantics_supplied
  orientation_convention :=
    source.orientation_convention
  orientation_convention_supplied :=
    source.orientation_convention_supplied
  boundary_reconstruction_compatibility :=
    source.boundary_reconstruction_compatibility
  boundary_reconstruction_compatibility_supplied :=
    source.boundary_reconstruction_compatibility_supplied
  flux_term_convergence_mode :=
    source.flux_term_convergence_mode
  flux_term_convergence_mode_supplied :=
    source.flux_term_convergence_mode_supplied
  finite_endpoint_flux_consistency_theorem :=
    source.finite_endpoint_flux_consistency_theorem
  finite_endpoint_flux_consistency_theorem_supplied :=
    source.finite_endpoint_flux_consistency_theorem_supplied
  trace_normal_derivative_convergence_statement :=
    source.trace_normal_derivative_convergence_statement
  trace_normal_derivative_convergence_statement_supplied :=
    source.trace_normal_derivative_convergence_statement_supplied
  orientation_compatibility_statement :=
    source.orientation_compatibility_statement
  orientation_compatibility_statement_supplied :=
    source.orientation_compatibility_statement_supplied
  semantics_supply_parent_boundary_trace_normal_derivative :=
    source.semantics_supply_parent_boundary_trace_normal_derivative
  orientation_supplies_parent_orientation :=
    source.orientation_supplies_parent_orientation
  channel_supplies_parent_contract_field := by
    intro hRep hBoundary hNormal hOrientation hReconstruct hMode hConsistency
    exact
      source.consistency_supplies_parent_endpoint_field
        hRep hBoundary hNormal hOrientation hReconstruct hMode hConsistency
  channel_supplies_parent_trace_normal_convergence := by
    intro hTrace hNormal
    exact
      source.trace_source_supplies_parent_trace_normal_convergence
        hTrace hNormal
  channel_supplies_parent_orientation_compatibility := by
    intro hCompat hOrientation
    exact
      source.orientation_source_supplies_parent_orientation_compatibility
        hCompat hOrientation

/-- A concrete source supplies the specialized endpoint-flux parent field. -/
theorem endpoint_flux_source_supplies_specialized_endpoint_field_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract) :
    contract.finite_endpoint_flux_to_continuum_boundary_flux := by
  exact
    specialized_endpoint_flux_evidence_supplies_endpoint_field_v0
      contract
      (endpointFluxChannelEvidenceOfSpecializedSource contract source)

/-- A concrete source supplies boundary trace/normal semantics. -/
theorem endpoint_flux_source_supplies_boundary_trace_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract) :
    target.boundary_trace_normal_derivative_semantics := by
  exact
    specialized_endpoint_flux_evidence_supplies_boundary_trace_v0
      contract
      (endpointFluxChannelEvidenceOfSpecializedSource contract source)

/-- A concrete source supplies trace-normal convergence. -/
theorem endpoint_flux_source_supplies_trace_normal_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract) :
    contract.trace_normal_derivative_convergence := by
  exact
    specialized_endpoint_flux_evidence_supplies_trace_normal_v0
      contract
      (endpointFluxChannelEvidenceOfSpecializedSource contract source)

/-- A concrete source supplies orientation compatibility. -/
theorem endpoint_flux_source_supplies_orientation_compatibility_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract) :
    contract.orientation_convention_compatible := by
  exact
    specialized_endpoint_flux_evidence_supplies_orientation_compatibility_v0
      contract
      (endpointFluxChannelEvidenceOfSpecializedSource contract source)

/--
Concrete endpoint source plus non-endpoint evidence builds the full A1A22
remaining-evidence package.
-/
def specializedRemainingEvidenceOfEndpointFluxSource
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    SpecializedA2A15A1RemainingEvidence contract :=
  specializedRemainingEvidenceOfEndpointFluxEvidence
    contract
    (endpointFluxChannelEvidenceOfSpecializedSource contract source)
    remaining

/-- Endpoint source plus non-endpoint evidence builds the specialized witness. -/
def specializedA2A15A1WitnessOfEndpointFluxSource
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (source : SpecializedEndpointFluxEvidenceSource contract)
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    AnalyticIntervalLiftWitness
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) :=
  specializedA2A15A1WitnessOfEndpointFluxEvidence
    contract
    (endpointFluxChannelEvidenceOfSpecializedSource contract source)
    remaining

/--
The false-endpoint specialized contract cannot have a concrete endpoint-flux
source, because any such source would supply the false endpoint field.
-/
theorem false_endpoint_contract_has_no_endpoint_flux_source_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    Not
      (Nonempty
        (SpecializedEndpointFluxEvidenceSource
          (specializedParentContractWithFalseEndpointFlux
            (target := target) evidenceOnly))) := by
  intro hSource
  rcases hSource with ⟨source⟩
  exact
    endpoint_flux_source_supplies_specialized_endpoint_field_v0
      (specializedParentContractWithFalseEndpointFlux
        (target := target) evidenceOnly)
      source

/-- Required source obligations after the A1A24 derivation attempt. -/
inductive EndpointFluxEvidenceDerivationObstruction where
  | noConcreteEndpointFluxEvidenceSource
  | noEndpointFluxRepresentationTheorem
  | noBoundaryTraceSemantics
  | noNormalDerivativeSemantics
  | noBoundaryReconstructionCompatibility
  | noFluxTermConvergenceMode
  | noFiniteEndpointFluxConsistencyTheorem
  | noTraceNormalDerivativeConvergenceTheorem
  | noOrientationConvention
  | noOrientationCompatibilityTheorem
  | noRemainingNonEndpointA2A15A1Evidence
  | noA2A15A1Closure
  | noA2A15BoundaryFluxClosure
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A24 obligations. -/
def endpointFluxEvidenceDerivationObstructionId :
    EndpointFluxEvidenceDerivationObstruction -> String
  | .noConcreteEndpointFluxEvidenceSource =>
      "A1A24_OBSTRUCTION_NO_CONCRETE_ENDPOINT_FLUX_EVIDENCE_SOURCE"
  | .noEndpointFluxRepresentationTheorem =>
      "A1A24_OBSTRUCTION_NO_ENDPOINT_FLUX_REPRESENTATION_THEOREM"
  | .noBoundaryTraceSemantics =>
      "A1A24_OBSTRUCTION_NO_BOUNDARY_TRACE_SEMANTICS"
  | .noNormalDerivativeSemantics =>
      "A1A24_OBSTRUCTION_NO_NORMAL_DERIVATIVE_SEMANTICS"
  | .noBoundaryReconstructionCompatibility =>
      "A1A24_OBSTRUCTION_NO_BOUNDARY_RECONSTRUCTION_COMPATIBILITY"
  | .noFluxTermConvergenceMode =>
      "A1A24_OBSTRUCTION_NO_FLUX_TERM_CONVERGENCE_MODE"
  | .noFiniteEndpointFluxConsistencyTheorem =>
      "A1A24_OBSTRUCTION_NO_FINITE_ENDPOINT_FLUX_CONSISTENCY_THEOREM"
  | .noTraceNormalDerivativeConvergenceTheorem =>
      "A1A24_OBSTRUCTION_NO_TRACE_NORMAL_DERIVATIVE_CONVERGENCE_THEOREM"
  | .noOrientationConvention =>
      "A1A24_OBSTRUCTION_NO_ORIENTATION_CONVENTION"
  | .noOrientationCompatibilityTheorem =>
      "A1A24_OBSTRUCTION_NO_ORIENTATION_COMPATIBILITY_THEOREM"
  | .noRemainingNonEndpointA2A15A1Evidence =>
      "A1A24_OBSTRUCTION_NO_REMAINING_NON_ENDPOINT_A2A15A1_EVIDENCE"
  | .noA2A15A1Closure =>
      "A1A24_OBSTRUCTION_NO_A2A15A1_CLOSURE"
  | .noA2A15BoundaryFluxClosure =>
      "A1A24_OBSTRUCTION_NO_A2A15_BOUNDARY_FLUX_CLOSURE"
  | .noPhase2Authorization =>
      "A1A24_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A24 derivation attempt. -/
def endpointFluxEvidenceDerivationObstructionsV0 :
    List EndpointFluxEvidenceDerivationObstruction :=
  [ .noConcreteEndpointFluxEvidenceSource
  , .noEndpointFluxRepresentationTheorem
  , .noBoundaryTraceSemantics
  , .noNormalDerivativeSemantics
  , .noBoundaryReconstructionCompatibility
  , .noFluxTermConvergenceMode
  , .noFiniteEndpointFluxConsistencyTheorem
  , .noTraceNormalDerivativeConvergenceTheorem
  , .noOrientationConvention
  , .noOrientationCompatibilityTheorem
  , .noRemainingNonEndpointA2A15A1Evidence
  , .noA2A15A1Closure
  , .noA2A15BoundaryFluxClosure
  , .noPhase2Authorization
  ]

/-- The A1A24 obstruction list is stable and explicit. -/
theorem endpoint_flux_evidence_derivation_obstructions_v0_expected :
    endpointFluxEvidenceDerivationObstructionsV0 =
      [ .noConcreteEndpointFluxEvidenceSource
      , .noEndpointFluxRepresentationTheorem
      , .noBoundaryTraceSemantics
      , .noNormalDerivativeSemantics
      , .noBoundaryReconstructionCompatibility
      , .noFluxTermConvergenceMode
      , .noFiniteEndpointFluxConsistencyTheorem
      , .noTraceNormalDerivativeConvergenceTheorem
      , .noOrientationConvention
      , .noOrientationCompatibilityTheorem
      , .noRemainingNonEndpointA2A15A1Evidence
      , .noA2A15A1Closure
      , .noA2A15BoundaryFluxClosure
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A24 records a concrete obstruction and conditional source bridge. -/
def endpointFluxEvidenceDerivationSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A24 successor kind is stable and explicit. -/
theorem endpoint_flux_evidence_derivation_successor_kinds_v0_expected :
    endpointFluxEvidenceDerivationSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for A1A24 endpoint-flux evidence derivation. -/
structure EndpointFluxEvidenceDerivationStatus where
  concrete_endpoint_flux_source_shape_defined : Prop
  concrete_endpoint_flux_source_shape_defined_supplied :
    concrete_endpoint_flux_source_shape_defined
  required_endpoint_obligations_stated : Prop
  required_endpoint_obligations_stated_supplied :
    required_endpoint_obligations_stated
  source_to_a1a23_channel_package_defined : Prop
  source_to_a1a23_channel_package_defined_supplied :
    source_to_a1a23_channel_package_defined
  source_supplies_specialized_endpoint_field : Prop
  source_supplies_specialized_endpoint_field_supplied :
    source_supplies_specialized_endpoint_field
  false_endpoint_source_refuted : Prop
  false_endpoint_source_refuted_supplied :
    false_endpoint_source_refuted
  concrete_endpoint_flux_source_supplied : Prop
  concrete_endpoint_flux_source_not_supplied :
    Not concrete_endpoint_flux_source_supplied
  remaining_non_endpoint_evidence_supplied : Prop
  remaining_non_endpoint_evidence_not_supplied :
    Not remaining_non_endpoint_evidence_supplied
  a2a15a1_closed : Prop
  a2a15a1_not_closed : Not a2a15a1_closed
  a2a15_boundary_flux_parent_closed : Prop
  a2a15_boundary_flux_parent_not_closed :
    Not a2a15_boundary_flux_parent_closed
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
Current A1A24 result: the endpoint source shape and bridge into A1A23 are
defined, but the source itself is not derived.
-/
def endpointFluxEvidenceDerivationStatusV0 :
    EndpointFluxEvidenceDerivationStatus where
  concrete_endpoint_flux_source_shape_defined := True
  concrete_endpoint_flux_source_shape_defined_supplied := True.intro
  required_endpoint_obligations_stated := True
  required_endpoint_obligations_stated_supplied := True.intro
  source_to_a1a23_channel_package_defined := True
  source_to_a1a23_channel_package_defined_supplied := True.intro
  source_supplies_specialized_endpoint_field := True
  source_supplies_specialized_endpoint_field_supplied := True.intro
  false_endpoint_source_refuted := True
  false_endpoint_source_refuted_supplied := True.intro
  concrete_endpoint_flux_source_supplied := False
  concrete_endpoint_flux_source_not_supplied := by
    intro h
    exact h
  remaining_non_endpoint_evidence_supplied := False
  remaining_non_endpoint_evidence_not_supplied := by
    intro h
    exact h
  a2a15a1_closed := False
  a2a15a1_not_closed := by
    intro h
    exact h
  a2a15_boundary_flux_parent_closed := False
  a2a15_boundary_flux_parent_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := a1a24EndpointFluxEvidenceDerivationSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A23SpecializedEndpointFluxEvidenceRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A24EndpointFluxEvidenceDerivationRetainedId
  outcome_id := endpointFluxEvidenceDerivationRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointFluxEvidenceDerivationSuccessorKindsV0
  obstruction_ids :=
    endpointFluxEvidenceDerivationObstructionsV0.map
      endpointFluxEvidenceDerivationObstructionId

/-- Short proof-facing status alias. -/
def endpointFluxEvidenceDerivationStatusReadoutV0 :
    EndpointFluxEvidenceDerivationStatus :=
  endpointFluxEvidenceDerivationStatusV0

/-- The concrete endpoint-flux source shape is defined. -/
theorem endpoint_flux_evidence_source_shape_defined_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.concrete_endpoint_flux_source_shape_defined := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.concrete_endpoint_flux_source_shape_defined_supplied

/-- The required endpoint obligations are stated. -/
theorem endpoint_flux_evidence_required_obligations_stated_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.required_endpoint_obligations_stated := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.required_endpoint_obligations_stated_supplied

/-- The source-to-A1A23 package bridge is defined. -/
theorem endpoint_flux_evidence_source_to_package_defined_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.source_to_a1a23_channel_package_defined := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.source_to_a1a23_channel_package_defined_supplied

/-- The source conditionally supplies the specialized endpoint field. -/
theorem endpoint_flux_evidence_source_supplies_endpoint_status_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.source_supplies_specialized_endpoint_field := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.source_supplies_specialized_endpoint_field_supplied

/-- False-endpoint source construction is refuted. -/
theorem endpoint_flux_evidence_false_endpoint_source_refuted_status_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.false_endpoint_source_refuted := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.false_endpoint_source_refuted_supplied

/-- The endpoint-flux source itself is not supplied by A1A24. -/
theorem endpoint_flux_evidence_source_not_supplied_v0 :
    Not
      (endpointFluxEvidenceDerivationStatusReadoutV0
        |>.concrete_endpoint_flux_source_supplied) := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.concrete_endpoint_flux_source_not_supplied

/-- Non-endpoint remaining evidence is not supplied by A1A24. -/
theorem endpoint_flux_evidence_non_endpoint_evidence_not_supplied_v0 :
    Not
      (endpointFluxEvidenceDerivationStatusReadoutV0
        |>.remaining_non_endpoint_evidence_supplied) := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.remaining_non_endpoint_evidence_not_supplied

/-- A2A15A1 is still not closed by A1A24. -/
theorem endpoint_flux_evidence_a2a15a1_not_closed_v0 :
    Not
      (endpointFluxEvidenceDerivationStatusReadoutV0 |>.a2a15a1_closed) := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.a2a15a1_not_closed

/-- A2A15 remains not closed by A1A24. -/
theorem endpoint_flux_evidence_a2a15_not_closed_v0 :
    Not
      (endpointFluxEvidenceDerivationStatusReadoutV0
        |>.a2a15_boundary_flux_parent_closed) := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.a2a15_boundary_flux_parent_not_closed

/-- Phase 2 remains unauthorized after A1A24. -/
theorem endpoint_flux_evidence_phase2_not_authorized_v0 :
    Not
      (endpointFluxEvidenceDerivationStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    endpointFluxEvidenceDerivationStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A24 retained blocker id is exposed. -/
theorem endpoint_flux_evidence_derivation_retained_id_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A24EndpointFluxEvidenceDerivationRetainedId := by
  rfl

/-- The A1A24 outcome id is exposed. -/
theorem endpoint_flux_evidence_derivation_outcome_id_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0.outcome_id =
      endpointFluxEvidenceDerivationRetainedOutcomeId := by
  rfl

/-- The A1A24 obstruction ids are exposed. -/
theorem endpoint_flux_evidence_derivation_obstruction_ids_v0 :
    endpointFluxEvidenceDerivationStatusReadoutV0.obstruction_ids =
      endpointFluxEvidenceDerivationObstructionsV0.map
        endpointFluxEvidenceDerivationObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianEndpointFluxEvidenceDerivation
end QFT
end ToeFormal
