/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation.lean

A1A28 endpoint orientation/trace compatibility obligation slice after the A1A27
convergence/consistency slice.

Scope:
- refine only the A1A25 orientation/trace compatibility subpackage
- split that subpackage into supplied orientation convention, supplied
  trace-normal convergence statement, supplied orientation-compatibility
  statement, and supplied bridges into the parent orientation, trace-normal,
  and orientation-compatibility fields
- prove those supplied pieces construct the A1A25 orientation/trace package for
  a supplied representation/semantics package
- retain full endpoint-source assembly, A2A15A1 closure, A2A15 closure, and
  Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianEndpointConvergenceConsistencyObligation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation

open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianEndpointSourceObligationSplit
open ContinuumSpatialGraphLaplacianEndpointRepresentationSemanticsObligation
open ContinuumSpatialGraphLaplacianEndpointConvergenceConsistencyObligation

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A28 orientation/trace endpoint slice. -/
def a1a28EndpointOrientationTraceCompatibilityObligationSurfaceId : String :=
  "A2A15A1A28_ENDPOINT_ORIENTATION_TRACE_COMPATIBILITY_OBLIGATION"

/-- Retained blocker after the A1A28 orientation/trace slice. -/
def phase1Blocker003A2A15A1A28EndpointOrientationTraceCompatibilityRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A28_ENDPOINT_ORIENTATION_TRACE_" ++
    "COMPATIBILITY_RETAINED"

/-- Outcome id for the retained A1A28 orientation/trace slice. -/
def endpointOrientationTraceCompatibilityRetainedOutcomeId : String :=
  "ENDPOINT_ORIENTATION_TRACE_COMPATIBILITY_RETAINED"

/-- Orientation convention obligation. -/
structure EndpointOrientationConventionObligation
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

/-- Trace-normal derivative convergence obligation. -/
structure EndpointTraceNormalConvergenceObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract) where
  trace_normal_derivative_convergence_statement : Prop
  trace_normal_derivative_convergence_statement_supplied :
    trace_normal_derivative_convergence_statement

/-- Orientation compatibility theorem obligation. -/
structure EndpointOrientationCompatibilityStatementObligation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract) where
  orientation_compatibility_statement : Prop
  orientation_compatibility_statement_supplied :
    orientation_compatibility_statement

/--
Bridges from supplied orientation/trace pieces to the parent orientation,
trace-normal convergence, and orientation-compatibility fields.
-/
structure EndpointOrientationTraceParentBridge
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation) where
  orientation_supplies_parent_orientation :
    orientation.orientation_convention ->
      target.orientation_convention_for_limit
  trace_source_supplies_parent_trace_normal_convergence :
    trace.trace_normal_derivative_convergence_statement ->
    representation.continuum_normal_derivative_semantics ->
      contract.trace_normal_derivative_convergence
  orientation_source_supplies_parent_orientation_compatibility :
    compatibility.orientation_compatibility_statement ->
    orientation.orientation_convention ->
      contract.orientation_convention_compatible

/--
The supplied A1A28 orientation, trace-normal, compatibility, and bridge pieces
construct the A1A25 orientation/trace package.
-/
def endpointOrientationTraceCompatibilityObligationsOfSuppliedPieces
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation)
    (bridge :
      EndpointOrientationTraceParentBridge
        contract representation orientation trace compatibility) :
    EndpointOrientationTraceCompatibilityObligations contract representation where
  orientation_convention :=
    orientation.orientation_convention
  orientation_convention_supplied :=
    orientation.orientation_convention_supplied
  trace_normal_derivative_convergence_statement :=
    trace.trace_normal_derivative_convergence_statement
  trace_normal_derivative_convergence_statement_supplied :=
    trace.trace_normal_derivative_convergence_statement_supplied
  orientation_compatibility_statement :=
    compatibility.orientation_compatibility_statement
  orientation_compatibility_statement_supplied :=
    compatibility.orientation_compatibility_statement_supplied
  orientation_supplies_parent_orientation :=
    bridge.orientation_supplies_parent_orientation
  trace_source_supplies_parent_trace_normal_convergence :=
    bridge.trace_source_supplies_parent_trace_normal_convergence
  orientation_source_supplies_parent_orientation_compatibility :=
    bridge.orientation_source_supplies_parent_orientation_compatibility

/-- Supplied A1A28 pieces construct the A1A25 orientation/trace package. -/
theorem endpoint_orientation_trace_supplied_pieces_construct_package_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation)
    (bridge :
      EndpointOrientationTraceParentBridge
        contract representation orientation trace compatibility) :
    Nonempty (EndpointOrientationTraceCompatibilityObligations
      contract representation) := by
  exact
    ⟨endpointOrientationTraceCompatibilityObligationsOfSuppliedPieces
      contract representation orientation trace compatibility bridge⟩

/-- Supplied A1A28 orientation evidence fills the parent orientation field. -/
theorem endpoint_orientation_trace_supplies_parent_orientation_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation)
    (bridge :
      EndpointOrientationTraceParentBridge
        contract representation orientation trace compatibility) :
    target.orientation_convention_for_limit := by
  exact
    bridge.orientation_supplies_parent_orientation
      orientation.orientation_convention_supplied

/-- Supplied A1A28 trace evidence fills parent trace-normal convergence. -/
theorem endpoint_orientation_trace_supplies_parent_trace_normal_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation)
    (bridge :
      EndpointOrientationTraceParentBridge
        contract representation orientation trace compatibility) :
    contract.trace_normal_derivative_convergence := by
  exact
    bridge.trace_source_supplies_parent_trace_normal_convergence
      trace.trace_normal_derivative_convergence_statement_supplied
      representation.continuum_normal_derivative_semantics_supplied

/-- Supplied A1A28 compatibility evidence fills parent orientation compatibility. -/
theorem endpoint_orientation_trace_supplies_parent_orientation_compatibility_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (representation :
      EndpointRepresentationSemanticsObligations contract)
    (orientation :
      EndpointOrientationConventionObligation contract representation)
    (trace :
      EndpointTraceNormalConvergenceObligation contract representation)
    (compatibility :
      EndpointOrientationCompatibilityStatementObligation
        contract representation)
    (bridge :
      EndpointOrientationTraceParentBridge
        contract representation orientation trace compatibility) :
    contract.orientation_convention_compatible := by
  exact
    bridge.orientation_source_supplies_parent_orientation_compatibility
      compatibility.orientation_compatibility_statement_supplied
      orientation.orientation_convention_supplied

/-- Remaining blockers after refining the orientation/trace obligation. -/
inductive EndpointOrientationTraceCompatibilityObstruction where
  | noRepresentationSemanticsDerivation
  | noOrientationConventionDerivation
  | noTraceNormalConvergenceTheoremDerivation
  | noOrientationCompatibilityTheoremDerivation
  | noParentOrientationBridgeDerivation
  | noParentTraceNormalBridgeDerivation
  | noParentOrientationCompatibilityBridgeDerivation
  | noRefinedEndpointSourceAssembly
  | noConcreteEndpointFluxEvidenceSource
  | noRemainingNonEndpointA2A15A1Evidence
  | noA2A15A1FinalWitness
  | noA2A15BoundaryFluxParent
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A28 objects. -/
def endpointOrientationTraceCompatibilityObstructionId :
    EndpointOrientationTraceCompatibilityObstruction -> String
  | .noRepresentationSemanticsDerivation =>
      "a1a28_obstruction_no_representation_semantics_derivation"
  | .noOrientationConventionDerivation =>
      "a1a28_obstruction_no_orientation_convention_derivation"
  | .noTraceNormalConvergenceTheoremDerivation =>
      "a1a28_obstruction_no_trace_normal_convergence_theorem_derivation"
  | .noOrientationCompatibilityTheoremDerivation =>
      "a1a28_obstruction_no_orientation_compatibility_theorem_derivation"
  | .noParentOrientationBridgeDerivation =>
      "a1a28_obstruction_no_parent_orientation_bridge_derivation"
  | .noParentTraceNormalBridgeDerivation =>
      "a1a28_obstruction_no_parent_trace_normal_bridge_derivation"
  | .noParentOrientationCompatibilityBridgeDerivation =>
      "a1a28_obstruction_no_parent_orientation_compatibility_bridge_derivation"
  | .noRefinedEndpointSourceAssembly =>
      "a1a28_obstruction_no_refined_endpoint_source_assembly"
  | .noConcreteEndpointFluxEvidenceSource =>
      "a1a28_obstruction_no_concrete_endpoint_flux_evidence_source"
  | .noRemainingNonEndpointA2A15A1Evidence =>
      "a1a28_obstruction_no_remaining_non_endpoint_a2a15a1_evidence"
  | .noA2A15A1FinalWitness =>
      "a1a28_obstruction_no_a2a15a1_final_witness"
  | .noA2A15BoundaryFluxParent =>
      "a1a28_obstruction_no_a2a15_boundary_flux_parent"
  | .noPhase2Authorization =>
      "a1a28_obstruction_no_phase2_authorization"

/-- Exact obstruction list after the A1A28 orientation/trace slice. -/
def endpointOrientationTraceCompatibilityObstructionsV0 :
    List EndpointOrientationTraceCompatibilityObstruction :=
  [ .noRepresentationSemanticsDerivation
  , .noOrientationConventionDerivation
  , .noTraceNormalConvergenceTheoremDerivation
  , .noOrientationCompatibilityTheoremDerivation
  , .noParentOrientationBridgeDerivation
  , .noParentTraceNormalBridgeDerivation
  , .noParentOrientationCompatibilityBridgeDerivation
  , .noRefinedEndpointSourceAssembly
  , .noConcreteEndpointFluxEvidenceSource
  , .noRemainingNonEndpointA2A15A1Evidence
  , .noA2A15A1FinalWitness
  , .noA2A15BoundaryFluxParent
  , .noPhase2Authorization
  ]

/-- The A1A28 obstruction list is stable and explicit. -/
theorem endpoint_orientation_trace_obstructions_v0_expected :
    endpointOrientationTraceCompatibilityObstructionsV0 =
      [ .noRepresentationSemanticsDerivation
      , .noOrientationConventionDerivation
      , .noTraceNormalConvergenceTheoremDerivation
      , .noOrientationCompatibilityTheoremDerivation
      , .noParentOrientationBridgeDerivation
      , .noParentTraceNormalBridgeDerivation
      , .noParentOrientationCompatibilityBridgeDerivation
      , .noRefinedEndpointSourceAssembly
      , .noConcreteEndpointFluxEvidenceSource
      , .noRemainingNonEndpointA2A15A1Evidence
      , .noA2A15A1FinalWitness
      , .noA2A15BoundaryFluxParent
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A28 records a subpackage constructor and concrete remaining obstruction. -/
def endpointOrientationTraceCompatibilitySuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The A1A28 successor kind is stable and explicit. -/
theorem endpoint_orientation_trace_successor_kinds_v0_expected :
    endpointOrientationTraceCompatibilitySuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A28 orientation/trace slice. -/
structure EndpointOrientationTraceCompatibilityStatus where
  orientation_convention_obligation_defined : Prop
  orientation_convention_obligation_defined_supplied :
    orientation_convention_obligation_defined
  trace_normal_convergence_obligation_defined : Prop
  trace_normal_convergence_obligation_defined_supplied :
    trace_normal_convergence_obligation_defined
  orientation_compatibility_obligation_defined : Prop
  orientation_compatibility_obligation_defined_supplied :
    orientation_compatibility_obligation_defined
  parent_orientation_trace_bridges_defined : Prop
  parent_orientation_trace_bridges_defined_supplied :
    parent_orientation_trace_bridges_defined
  supplied_pieces_construct_a1a25_orientation_package : Prop
  supplied_pieces_construct_a1a25_orientation_package_supplied :
    supplied_pieces_construct_a1a25_orientation_package
  supplied_pieces_supply_parent_orientation_fields : Prop
  supplied_pieces_supply_parent_orientation_fields_supplied :
    supplied_pieces_supply_parent_orientation_fields
  orientation_trace_derivation_supplied : Prop
  orientation_trace_derivation_not_supplied :
    Not orientation_trace_derivation_supplied
  refined_endpoint_source_assembly_supplied : Prop
  refined_endpoint_source_assembly_not_supplied :
    Not refined_endpoint_source_assembly_supplied
  endpoint_source_supplied : Prop
  endpoint_source_not_supplied : Not endpoint_source_supplied
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
Current A1A28 result: the orientation/trace subpackage has a supplied piece
interface, but actual derivation and endpoint-source assembly remain retained.
-/
def endpointOrientationTraceCompatibilityStatusV0 :
    EndpointOrientationTraceCompatibilityStatus where
  orientation_convention_obligation_defined := True
  orientation_convention_obligation_defined_supplied := True.intro
  trace_normal_convergence_obligation_defined := True
  trace_normal_convergence_obligation_defined_supplied := True.intro
  orientation_compatibility_obligation_defined := True
  orientation_compatibility_obligation_defined_supplied := True.intro
  parent_orientation_trace_bridges_defined := True
  parent_orientation_trace_bridges_defined_supplied := True.intro
  supplied_pieces_construct_a1a25_orientation_package := True
  supplied_pieces_construct_a1a25_orientation_package_supplied := True.intro
  supplied_pieces_supply_parent_orientation_fields := True
  supplied_pieces_supply_parent_orientation_fields_supplied := True.intro
  orientation_trace_derivation_supplied := False
  orientation_trace_derivation_not_supplied := by
    intro h
    exact h
  refined_endpoint_source_assembly_supplied := False
  refined_endpoint_source_assembly_not_supplied := by
    intro h
    exact h
  endpoint_source_supplied := False
  endpoint_source_not_supplied := by
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
  surface_id := a1a28EndpointOrientationTraceCompatibilityObligationSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A27EndpointConvergenceConsistencyRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A28EndpointOrientationTraceCompatibilityRetainedId
  outcome_id := endpointOrientationTraceCompatibilityRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointOrientationTraceCompatibilitySuccessorKindsV0
  obstruction_ids :=
    endpointOrientationTraceCompatibilityObstructionsV0.map
      endpointOrientationTraceCompatibilityObstructionId

/-- Short proof-facing status alias. -/
def endpointOrientationTraceCompatibilityStatusReadoutV0 :
    EndpointOrientationTraceCompatibilityStatus :=
  endpointOrientationTraceCompatibilityStatusV0

/-- The orientation convention obligation is defined. -/
theorem endpoint_orientation_convention_obligation_defined_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.orientation_convention_obligation_defined := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.orientation_convention_obligation_defined_supplied

/-- The trace-normal convergence obligation is defined. -/
theorem endpoint_trace_normal_convergence_obligation_defined_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.trace_normal_convergence_obligation_defined := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.trace_normal_convergence_obligation_defined_supplied

/-- The orientation compatibility obligation is defined. -/
theorem endpoint_orientation_compatibility_obligation_defined_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.orientation_compatibility_obligation_defined := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.orientation_compatibility_obligation_defined_supplied

/-- The parent orientation/trace bridges are defined. -/
theorem endpoint_orientation_trace_parent_bridges_defined_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.parent_orientation_trace_bridges_defined := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.parent_orientation_trace_bridges_defined_supplied

/-- A1A28 records the supplied-pieces-to-A1A25-package constructor. -/
theorem endpoint_orientation_trace_constructor_defined_status_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.supplied_pieces_construct_a1a25_orientation_package := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.supplied_pieces_construct_a1a25_orientation_package_supplied

/-- A1A28 records routing into the parent orientation/trace fields. -/
theorem endpoint_orientation_trace_parent_fields_status_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.supplied_pieces_supply_parent_orientation_fields := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.supplied_pieces_supply_parent_orientation_fields_supplied

/-- The analytic orientation/trace derivation is not supplied by A1A28. -/
theorem endpoint_orientation_trace_derivation_not_supplied_v0 :
    Not
      (endpointOrientationTraceCompatibilityStatusReadoutV0
        |>.orientation_trace_derivation_supplied) := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.orientation_trace_derivation_not_supplied

/-- The refined endpoint source is not assembled by A1A28. -/
theorem endpoint_orientation_trace_refined_source_not_assembled_v0 :
    Not
      (endpointOrientationTraceCompatibilityStatusReadoutV0
        |>.refined_endpoint_source_assembly_supplied) := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.refined_endpoint_source_assembly_not_supplied

/-- The full endpoint source is not supplied by A1A28. -/
theorem endpoint_orientation_trace_source_not_supplied_v0 :
    Not
      (endpointOrientationTraceCompatibilityStatusReadoutV0
        |>.endpoint_source_supplied) := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.endpoint_source_not_supplied

/-- A1A28 does not supply a final A2A15A1 witness. -/
theorem endpoint_orientation_trace_final_witness_not_supplied_v0 :
    Not
      (endpointOrientationTraceCompatibilityStatusReadoutV0
        |>.a2a15a1_final_witness_supplied) := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.a2a15a1_final_witness_not_supplied

/-- Phase 2 remains unauthorized after A1A28. -/
theorem endpoint_orientation_trace_phase2_not_authorized_v0 :
    Not
      (endpointOrientationTraceCompatibilityStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    endpointOrientationTraceCompatibilityStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A28 retained blocker id is exposed. -/
theorem endpoint_orientation_trace_retained_id_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A28EndpointOrientationTraceCompatibilityRetainedId := by
  rfl

/-- The A1A28 outcome id is exposed. -/
theorem endpoint_orientation_trace_outcome_id_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0.outcome_id =
      endpointOrientationTraceCompatibilityRetainedOutcomeId := by
  rfl

/-- The A1A28 obstruction ids are exposed. -/
theorem endpoint_orientation_trace_obstruction_ids_v0 :
    endpointOrientationTraceCompatibilityStatusReadoutV0.obstruction_ids =
      endpointOrientationTraceCompatibilityObstructionsV0.map
        endpointOrientationTraceCompatibilityObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation
end QFT
end ToeFormal
