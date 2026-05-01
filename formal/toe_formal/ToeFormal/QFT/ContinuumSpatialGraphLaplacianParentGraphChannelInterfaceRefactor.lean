/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor.lean

A1A21 parent graph-channel interface specialization/refactor after the A1A20
abstraction obstruction.

Scope:
- define a specialized parent graph-channel contract shape whose graph-channel
  proposition is definitionally the A1A16 actual-error stencil-limit proposition
- construct the legacy `AnalyticIntervalLiftConvergenceContract` view exported
  by this specialized shape
- prove A1A16 actual-error evidence supplies that specialized parent graph field
- prove the A1A19 proposition-equality bridge is automatic for the specialized
  legacy view
- retain global parent-interface migration, A2A15A1 closure, and Phase 2
  authorization
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianParentInterfaceTooAbstractReview

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
open ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface
open ContinuumSpatialGraphLaplacianParentInterfaceEquivalenceBridge
open ContinuumSpatialGraphLaplacianParentInterfaceTooAbstractReview

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A21 parent graph-channel interface refactor. -/
def a1a21ParentGraphChannelInterfaceRefactorSurfaceId : String :=
  "A2A15A1A21_PARENT_GRAPH_CHANNEL_INTERFACE_REFACTOR"

/-- Retained blocker while the specialized interface is not globally migrated. -/
def phase1Blocker003A2A15A1A21ParentGraphChannelInterfaceRefactorRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A21_PARENT_GRAPH_CHANNEL_INTERFACE_" ++
    "REFACTOR_RETAINED"

/-- Outcome id for the retained A1A21 refactor slice. -/
def parentGraphChannelInterfaceRefactorRetainedOutcomeId : String :=
  "PARENT_GRAPH_CHANNEL_INTERFACE_REFACTOR_RETAINED"

/--
Specialized parent contract shape for the graph-channel slot.

Compared with `AnalyticIntervalLiftConvergenceContract`, the graph-channel
field is not an arbitrary `Prop`.  It is definitionally the A1A16 actual graph
error stencil-limit proposition carried by `evidenceOnly`.
-/
structure ActualErrorSpecializedParentGraphChannelContract
    {ContinuumPoint : Type}
    {f : Real -> Real}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (x C : Real) where
  evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C
  ApproximationIndex : Type
  sample :
    ApproximationIndex ->
      ContinuumField ContinuumPoint ->
      ContinuumField TwoPointSpatialInterval
  reconstruct :
    ApproximationIndex ->
      ContinuumField TwoPointSpatialInterval ->
      ContinuumField ContinuumPoint
  finite_endpoint_flux_to_continuum_boundary_flux : Prop
  finite_raw_ibp_to_continuum_green_identity : Prop
  finite_pairing_to_continuum_pairing : Prop
  trace_normal_derivative_convergence : Prop
  domain_regular_for_limit_passage : Prop
  orientation_convention_compatible : Prop
  separating_test_class_for_limit : Prop
  contract_implies_raw_spatial_ibp :
    actualGraphErrorRestrictedParentGraphChannelField evidenceOnly ->
    finite_pairing_to_continuum_pairing ->
    finite_raw_ibp_to_continuum_green_identity ->
    domain_regular_for_limit_passage ->
      RawSpatialIntegrationByPartsStatement
        target.continuum_problem
        target.continuum_raw_boundary_flux
  contract_implies_boundary_flux_representation :
    finite_endpoint_flux_to_continuum_boundary_flux ->
    trace_normal_derivative_convergence ->
    orientation_convention_compatible ->
      BoundaryFluxRepresentationStatement
        target.continuum_problem
        target.continuum_raw_boundary_flux

/-- The refactored graph-channel field is definitionally actual-error convergence. -/
def actualErrorSpecializedParentGraphChannelField
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) : Prop :=
  actualGraphErrorRestrictedParentGraphChannelField contract.evidenceOnly

/-- The specialized graph-channel field is exactly the actual-error field. -/
theorem actual_error_specialized_parent_graph_channel_field_eq_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    actualErrorSpecializedParentGraphChannelField contract =
      actualGraphErrorRestrictedParentGraphChannelField
        contract.evidenceOnly := by
  rfl

/--
Legacy parent-contract view exported by the specialized graph-channel contract.

This keeps compatibility with existing users while replacing only the
graph-channel slot with the refactored actual-error proposition.
-/
def analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    AnalyticIntervalLiftConvergenceContract target where
  ApproximationIndex := contract.ApproximationIndex
  sample := contract.sample
  reconstruct := contract.reconstruct
  graph_laplacian_action_to_continuum_laplacian :=
    actualErrorSpecializedParentGraphChannelField contract
  finite_endpoint_flux_to_continuum_boundary_flux :=
    contract.finite_endpoint_flux_to_continuum_boundary_flux
  finite_raw_ibp_to_continuum_green_identity :=
    contract.finite_raw_ibp_to_continuum_green_identity
  finite_pairing_to_continuum_pairing :=
    contract.finite_pairing_to_continuum_pairing
  trace_normal_derivative_convergence :=
    contract.trace_normal_derivative_convergence
  domain_regular_for_limit_passage :=
    contract.domain_regular_for_limit_passage
  orientation_convention_compatible :=
    contract.orientation_convention_compatible
  separating_test_class_for_limit :=
    contract.separating_test_class_for_limit
  contract_implies_raw_spatial_ibp := by
    intro hGraph hPairing hRaw hDomain
    exact
      contract.contract_implies_raw_spatial_ibp
        hGraph hPairing hRaw hDomain
  contract_implies_boundary_flux_representation := by
    intro hEndpointFlux hTrace hOrientation
    exact
      contract.contract_implies_boundary_flux_representation
        hEndpointFlux hTrace hOrientation

/-- The specialized legacy view ties the parent graph field to actual-error evidence. -/
theorem specialized_parent_legacy_graph_field_eq_actual_error_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
      contract).graph_laplacian_action_to_continuum_laplacian =
      actualGraphErrorRestrictedParentGraphChannelField
        contract.evidenceOnly := by
  rfl

/-- A1A16 actual-error evidence supplies the specialized parent graph field. -/
theorem actual_error_supplies_specialized_parent_graph_field_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
      contract).graph_laplacian_action_to_continuum_laplacian := by
  exact
    actual_graph_error_restricted_parent_graph_channel_field_v0
      contract.evidenceOnly

/--
The A1A19 proposition-equality bridge is automatic for the specialized legacy
view.
-/
theorem specialized_parent_legacy_actual_error_equality_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    ParentGraphChannelActualErrorPropositionEquality
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract)
      contract.evidenceOnly := by
  rfl

/-- The specialized legacy view is filled through the A1A19 equality theorem. -/
theorem specialized_parent_legacy_filled_via_a1a19_equality_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) :
    (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
      contract).graph_laplacian_action_to_continuum_laplacian := by
  exact
    actual_graph_error_satisfies_parent_given_interface_equality_v0
      contract.evidenceOnly
      (specialized_parent_legacy_actual_error_equality_v0 contract)

/-- Remaining objects after the A1A21 parent-interface refactor slice. -/
inductive ParentGraphChannelInterfaceRefactorObstruction where
  | noGlobalMigrationOfParentInterface
  | currentParentInterfaceStillAvailable
  | noSpecializedA2A15A1Witness
  | noFiniteEndpointFluxClosure
  | noFiniteRawIBPGreenIdentityClosure
  | noContinuumLaplacianSemanticClosure
  | noOperatorDomainClosureFromActualError
  | noParentGraphRelation
  | noA2A15A1AssemblyReview
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A21 objects. -/
def parentGraphChannelInterfaceRefactorObstructionId :
    ParentGraphChannelInterfaceRefactorObstruction -> String
  | .noGlobalMigrationOfParentInterface =>
      "A1A21_OBSTRUCTION_NO_GLOBAL_MIGRATION_OF_PARENT_INTERFACE"
  | .currentParentInterfaceStillAvailable =>
      "A1A21_OBSTRUCTION_CURRENT_PARENT_INTERFACE_STILL_AVAILABLE"
  | .noSpecializedA2A15A1Witness =>
      "A1A21_OBSTRUCTION_NO_SPECIALIZED_A2A15A1_WITNESS"
  | .noFiniteEndpointFluxClosure =>
      "A1A21_OBSTRUCTION_NO_FINITE_ENDPOINT_FLUX_CLOSURE"
  | .noFiniteRawIBPGreenIdentityClosure =>
      "A1A21_OBSTRUCTION_NO_FINITE_RAW_IBP_GREEN_IDENTITY_CLOSURE"
  | .noContinuumLaplacianSemanticClosure =>
      "A1A21_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTIC_CLOSURE"
  | .noOperatorDomainClosureFromActualError =>
      "A1A21_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FROM_ACTUAL_ERROR"
  | .noParentGraphRelation =>
      "A1A21_OBSTRUCTION_NO_PARENT_GRAPH_RELATION"
  | .noA2A15A1AssemblyReview =>
      "A1A21_OBSTRUCTION_NO_A2A15A1_ASSEMBLY_REVIEW"
  | .noPhase2Authorization =>
      "A1A21_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A21 refactor slice. -/
def parentGraphChannelInterfaceRefactorObstructionsV0 :
    List ParentGraphChannelInterfaceRefactorObstruction :=
  [ .noGlobalMigrationOfParentInterface
  , .currentParentInterfaceStillAvailable
  , .noSpecializedA2A15A1Witness
  , .noFiniteEndpointFluxClosure
  , .noFiniteRawIBPGreenIdentityClosure
  , .noContinuumLaplacianSemanticClosure
  , .noOperatorDomainClosureFromActualError
  , .noParentGraphRelation
  , .noA2A15A1AssemblyReview
  , .noPhase2Authorization
  ]

/-- The A1A21 obstruction list is stable and explicit. -/
theorem parent_graph_channel_interface_refactor_obstructions_v0_expected :
    parentGraphChannelInterfaceRefactorObstructionsV0 =
      [ .noGlobalMigrationOfParentInterface
      , .currentParentInterfaceStillAvailable
      , .noSpecializedA2A15A1Witness
      , .noFiniteEndpointFluxClosure
      , .noFiniteRawIBPGreenIdentityClosure
      , .noContinuumLaplacianSemanticClosure
      , .noOperatorDomainClosureFromActualError
      , .noParentGraphRelation
      , .noA2A15A1AssemblyReview
      , .noPhase2Authorization
      ] := by
  rfl

/-- This successor proves specialized transport and records retained migration. -/
def parentGraphChannelInterfaceRefactorSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A21 successor kind records proof progress plus retained migration. -/
theorem parent_graph_channel_interface_refactor_successor_kinds_v0_expected :
    parentGraphChannelInterfaceRefactorSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A21 parent-interface refactor slice. -/
structure ParentGraphChannelInterfaceRefactorStatus where
  specialized_interface_defined : Prop
  specialized_interface_defined_supplied : specialized_interface_defined
  graph_field_definitionally_actual_error : Prop
  graph_field_definitionally_actual_error_supplied :
    graph_field_definitionally_actual_error
  legacy_view_exports_specialized_field : Prop
  legacy_view_exports_specialized_field_supplied :
    legacy_view_exports_specialized_field
  actual_error_supplies_specialized_field : Prop
  actual_error_supplies_specialized_field_supplied :
    actual_error_supplies_specialized_field
  a1a19_equality_bridge_automatic : Prop
  a1a19_equality_bridge_automatic_supplied :
    a1a19_equality_bridge_automatic
  global_parent_interface_migrated : Prop
  global_parent_interface_not_migrated :
    Not global_parent_interface_migrated
  current_parent_interface_closed : Prop
  current_parent_interface_not_closed :
    Not current_parent_interface_closed
  a2a15a1_ready_for_review : Prop
  a2a15a1_not_ready_for_review : Not a2a15a1_ready_for_review
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
Current A1A21 result: a specialized parent graph-channel contract shape fixes
the A1A graph slot locally, but global parent-interface migration is retained.
-/
def parentGraphChannelInterfaceRefactorStatusV0 :
    ParentGraphChannelInterfaceRefactorStatus where
  specialized_interface_defined := True
  specialized_interface_defined_supplied := True.intro
  graph_field_definitionally_actual_error := True
  graph_field_definitionally_actual_error_supplied := True.intro
  legacy_view_exports_specialized_field := True
  legacy_view_exports_specialized_field_supplied := True.intro
  actual_error_supplies_specialized_field := True
  actual_error_supplies_specialized_field_supplied := True.intro
  a1a19_equality_bridge_automatic := True
  a1a19_equality_bridge_automatic_supplied := True.intro
  global_parent_interface_migrated := False
  global_parent_interface_not_migrated := by
    intro h
    exact h
  current_parent_interface_closed := False
  current_parent_interface_not_closed := by
    intro h
    exact h
  a2a15a1_ready_for_review := False
  a2a15a1_not_ready_for_review := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := a1a21ParentGraphChannelInterfaceRefactorSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A20ParentInterfaceTooAbstractRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A21ParentGraphChannelInterfaceRefactorRetainedId
  outcome_id := parentGraphChannelInterfaceRefactorRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := parentGraphChannelInterfaceRefactorSuccessorKindsV0
  obstruction_ids :=
    parentGraphChannelInterfaceRefactorObstructionsV0.map
      parentGraphChannelInterfaceRefactorObstructionId

/-- Short proof-facing status alias. -/
def parentGraphChannelInterfaceRefactorStatusReadoutV0 :
    ParentGraphChannelInterfaceRefactorStatus :=
  parentGraphChannelInterfaceRefactorStatusV0

/-- The specialized parent graph-channel interface is defined. -/
theorem parent_graph_channel_interface_refactor_defined_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.specialized_interface_defined := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.specialized_interface_defined_supplied

/-- The specialized graph field is definitionally actual-error convergence. -/
theorem parent_graph_channel_interface_refactor_field_tied_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.graph_field_definitionally_actual_error := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.graph_field_definitionally_actual_error_supplied

/-- The legacy view exports the specialized graph field. -/
theorem parent_graph_channel_interface_refactor_legacy_view_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.legacy_view_exports_specialized_field := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.legacy_view_exports_specialized_field_supplied

/-- A1A16 actual-error evidence supplies the specialized parent field. -/
theorem parent_graph_channel_interface_refactor_actual_error_supplies_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.actual_error_supplies_specialized_field := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.actual_error_supplies_specialized_field_supplied

/-- The A1A19 equality bridge is automatic for the specialized legacy view. -/
theorem parent_graph_channel_interface_refactor_equality_automatic_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.a1a19_equality_bridge_automatic := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.a1a19_equality_bridge_automatic_supplied

/-- Global migration of the parent interface is not completed by A1A21. -/
theorem parent_graph_channel_interface_refactor_global_migration_retained_v0 :
    Not
      (parentGraphChannelInterfaceRefactorStatusReadoutV0
        |>.global_parent_interface_migrated) := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.global_parent_interface_not_migrated

/-- The current parent interface is not closed by A1A21 alone. -/
theorem parent_graph_channel_interface_refactor_current_parent_not_closed_v0 :
    Not
      (parentGraphChannelInterfaceRefactorStatusReadoutV0
        |>.current_parent_interface_closed) := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.current_parent_interface_not_closed

/-- A2A15A1 remains not ready for review after A1A21. -/
theorem parent_graph_channel_interface_refactor_a2a15a1_not_ready_v0 :
    Not
      (parentGraphChannelInterfaceRefactorStatusReadoutV0
        |>.a2a15a1_ready_for_review) := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.a2a15a1_not_ready_for_review

/-- Phase 2 remains unauthorized after A1A21. -/
theorem parent_graph_channel_interface_refactor_phase2_not_authorized_v0 :
    Not
      (parentGraphChannelInterfaceRefactorStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    parentGraphChannelInterfaceRefactorStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A21 retained blocker id is exposed. -/
theorem parent_graph_channel_interface_refactor_retained_id_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A21ParentGraphChannelInterfaceRefactorRetainedId := by
  rfl

/-- The A1A21 outcome id is exposed. -/
theorem parent_graph_channel_interface_refactor_outcome_id_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0.outcome_id =
      parentGraphChannelInterfaceRefactorRetainedOutcomeId := by
  rfl

/-- The A1A21 obstruction ids are exposed. -/
theorem parent_graph_channel_interface_refactor_obstruction_ids_v0 :
    parentGraphChannelInterfaceRefactorStatusReadoutV0.obstruction_ids =
      parentGraphChannelInterfaceRefactorObstructionsV0.map
        parentGraphChannelInterfaceRefactorObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
end QFT
end ToeFormal
