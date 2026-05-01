/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface.lean

A1A18 restricted parent graph-channel interface after the A1A17
semantic-map-free counterexample.

Scope:
- define a restricted parent graph-channel interface whose graph-channel field
  is exactly the actual graph-error convergence evidence
- prove that the A1A16 actual graph-error evidence satisfies that restricted
  interface
- state the bridge condition needed to move from the restricted interface to
  the current arbitrary parent `AnalyticIntervalLiftConvergenceContract`
- keep arbitrary parent-interface closure, A2A15A1 closure, Phase 2
  authorization, and Phase 0-5 completion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface

open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
open ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound
open ContinuumSpatialGraphLaplacianActualGraphStencilErrorIdentification
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A18 restricted parent graph-channel interface. -/
def a1a18RestrictedParentGraphChannelInterfaceSurfaceId : String :=
  "A2A15A1A18_RESTRICTED_PARENT_GRAPH_CHANNEL_INTERFACE"

/-- Retained blocker after restricting the parent interface but not deriving the bridge. -/
def phase1Blocker003A2A15A1A18RestrictedParentGraphChannelInterfaceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A18_RESTRICTED_PARENT_GRAPH_CHANNEL_" ++
    "INTERFACE_RETAINED"

/-- Outcome id for the retained A1A18 restricted-interface slice. -/
def restrictedParentGraphChannelInterfaceRetainedOutcomeId : String :=
  "RESTRICTED_PARENT_GRAPH_CHANNEL_INTERFACE_RETAINED"

/--
The restricted parent graph-channel proposition selected by A1A18.

Unlike the arbitrary parent contract field from A1A17, this proposition is
definitionally the actual graph-error stencil-limit evidence constructed from
A1A16.
-/
def actualGraphErrorRestrictedParentGraphChannelField
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) : Prop :=
  (uniformMeshConvergenceEvidenceOfActualGraphErrorEvidenceOnly
    evidenceOnly).stencil_error_tends_to_zero

/-- A1A16 actual graph-error evidence supplies the restricted graph-channel field. -/
theorem actual_graph_error_restricted_parent_graph_channel_field_v0
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    actualGraphErrorRestrictedParentGraphChannelField evidenceOnly := by
  simpa [actualGraphErrorRestrictedParentGraphChannelField] using
    actual_graph_error_evidence_only_derives_stencil_limit_v0 evidenceOnly

/--
Restricted parent graph-channel interface.

This is intentionally narrower than `AnalyticIntervalLiftConvergenceContract`:
it keeps only the graph-channel field and requires that field to be exactly
the A1A16 actual graph-error convergence proposition.
-/
structure RestrictedParentGraphChannelInterface
    {f : Real -> Real}
    (x C : Real) where
  evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C
  graph_laplacian_action_to_continuum_laplacian : Prop
  graph_channel_is_actual_error_convergence :
    graph_laplacian_action_to_continuum_laplacian =
      actualGraphErrorRestrictedParentGraphChannelField evidenceOnly

/-- The restricted interface canonically associated to A1A16 actual-error evidence. -/
def restrictedParentGraphChannelInterfaceOfActualGraphError
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    RestrictedParentGraphChannelInterface (f := f) x C where
  evidenceOnly := evidenceOnly
  graph_laplacian_action_to_continuum_laplacian :=
    actualGraphErrorRestrictedParentGraphChannelField evidenceOnly
  graph_channel_is_actual_error_convergence := rfl

/-- A1A16 satisfies the restricted parent graph-channel interface. -/
theorem actual_graph_error_satisfies_restricted_parent_interface_v0
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    (restrictedParentGraphChannelInterfaceOfActualGraphError
      evidenceOnly).graph_laplacian_action_to_continuum_laplacian := by
  exact actual_graph_error_restricted_parent_graph_channel_field_v0
    evidenceOnly

/--
Bridge condition from the restricted A1A18 interface to the arbitrary parent
graph-channel field.

A1A18 states this condition but does not derive it.  Supplying this bridge is
the remaining semantic-map work needed to return to the current arbitrary
parent interface.
-/
structure RestrictedToArbitraryParentGraphChannelBridge
    {ContinuumPoint : Type}
    {f : Real -> Real}
    {x C : Real}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract target)
    (restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C) where
  restricted_graph_channel_supplies_parent :
    restrictedInterface.graph_laplacian_action_to_continuum_laplacian ->
      parentContract.graph_laplacian_action_to_continuum_laplacian

/-- A supplied bridge moves restricted-interface evidence into the parent field. -/
theorem restricted_parent_interface_bridge_supplies_parent_graph_channel_field
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C}
    (bridge :
      RestrictedToArbitraryParentGraphChannelBridge
        target parentContract restrictedInterface)
    (hRestricted :
      restrictedInterface.graph_laplacian_action_to_continuum_laplacian) :
    parentContract.graph_laplacian_action_to_continuum_laplacian := by
  exact bridge.restricted_graph_channel_supplies_parent hRestricted

/-- A1A16 fills the arbitrary parent graph field if the restricted bridge is supplied. -/
theorem actual_graph_error_satisfies_parent_given_restricted_bridge_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C)
    (bridge :
      RestrictedToArbitraryParentGraphChannelBridge
        target
        parentContract
        (restrictedParentGraphChannelInterfaceOfActualGraphError
          evidenceOnly)) :
    parentContract.graph_laplacian_action_to_continuum_laplacian := by
  exact
    restricted_parent_interface_bridge_supplies_parent_graph_channel_field
      bridge
      (actual_graph_error_satisfies_restricted_parent_interface_v0
        evidenceOnly)

/-- Remaining objects after the A1A18 restricted-interface slice. -/
inductive RestrictedParentGraphChannelInterfaceObstruction where
  | noRestrictedToArbitraryParentBridge
  | noContinuumLaplacianSemanticClosure
  | noOperatorDomainClosureFromActualError
  | noParentGraphRelation
  | noA2A15A1AssemblyReview
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A18 objects. -/
def restrictedParentGraphChannelInterfaceObstructionId :
    RestrictedParentGraphChannelInterfaceObstruction -> String
  | .noRestrictedToArbitraryParentBridge =>
      "A1A18_OBSTRUCTION_NO_RESTRICTED_TO_ARBITRARY_PARENT_BRIDGE"
  | .noContinuumLaplacianSemanticClosure =>
      "A1A18_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTIC_CLOSURE"
  | .noOperatorDomainClosureFromActualError =>
      "A1A18_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FROM_ACTUAL_ERROR"
  | .noParentGraphRelation =>
      "A1A18_OBSTRUCTION_NO_PARENT_GRAPH_RELATION"
  | .noA2A15A1AssemblyReview =>
      "A1A18_OBSTRUCTION_NO_A2A15A1_ASSEMBLY_REVIEW"
  | .noPhase2Authorization =>
      "A1A18_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A18 restricted-interface slice. -/
def restrictedParentGraphChannelInterfaceObstructionsV0 :
    List RestrictedParentGraphChannelInterfaceObstruction :=
  [ .noRestrictedToArbitraryParentBridge
  , .noContinuumLaplacianSemanticClosure
  , .noOperatorDomainClosureFromActualError
  , .noParentGraphRelation
  , .noA2A15A1AssemblyReview
  , .noPhase2Authorization
  ]

/-- The A1A18 obstruction list is stable and explicit. -/
theorem restricted_parent_graph_channel_interface_obstructions_v0_expected :
    restrictedParentGraphChannelInterfaceObstructionsV0 =
      [ .noRestrictedToArbitraryParentBridge
      , .noContinuumLaplacianSemanticClosure
      , .noOperatorDomainClosureFromActualError
      , .noParentGraphRelation
      , .noA2A15A1AssemblyReview
      , .noPhase2Authorization
      ] := by
  rfl

/-- This successor proves the restricted field and records the retained bridge. -/
def restrictedParentGraphChannelInterfaceSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A18 successor kind records proof progress plus retained obstruction. -/
theorem restricted_parent_graph_channel_interface_successor_kinds_v0_expected :
    restrictedParentGraphChannelInterfaceSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A18 restricted parent graph-channel interface. -/
structure RestrictedParentGraphChannelInterfaceStatus where
  restricted_interface_defined : Prop
  restricted_interface_defined_supplied :
    restricted_interface_defined
  graph_channel_field_is_actual_error_convergence : Prop
  graph_channel_field_is_actual_error_convergence_supplied :
    graph_channel_field_is_actual_error_convergence
  actual_error_satisfies_restricted_interface : Prop
  actual_error_satisfies_restricted_interface_supplied :
    actual_error_satisfies_restricted_interface
  restricted_to_arbitrary_bridge_condition_stated : Prop
  restricted_to_arbitrary_bridge_condition_stated_supplied :
    restricted_to_arbitrary_bridge_condition_stated
  restricted_to_arbitrary_bridge_derived : Prop
  restricted_to_arbitrary_bridge_not_derived :
    Not restricted_to_arbitrary_bridge_derived
  arbitrary_parent_interface_closed : Prop
  arbitrary_parent_interface_not_closed :
    Not arbitrary_parent_interface_closed
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
Current A1A18 result: actual graph-error evidence satisfies the restricted
parent graph-channel interface, but the bridge to arbitrary parent contracts
is still retained.
-/
def restrictedParentGraphChannelInterfaceStatusV0 :
    RestrictedParentGraphChannelInterfaceStatus where
  restricted_interface_defined := True
  restricted_interface_defined_supplied := True.intro
  graph_channel_field_is_actual_error_convergence := True
  graph_channel_field_is_actual_error_convergence_supplied := True.intro
  actual_error_satisfies_restricted_interface := True
  actual_error_satisfies_restricted_interface_supplied := True.intro
  restricted_to_arbitrary_bridge_condition_stated := True
  restricted_to_arbitrary_bridge_condition_stated_supplied := True.intro
  restricted_to_arbitrary_bridge_derived := False
  restricted_to_arbitrary_bridge_not_derived := by
    intro h
    exact h
  arbitrary_parent_interface_closed := False
  arbitrary_parent_interface_not_closed := by
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
  surface_id := a1a18RestrictedParentGraphChannelInterfaceSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A17ParentGraphChannelInterfaceMapRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A18RestrictedParentGraphChannelInterfaceRetainedId
  outcome_id := restrictedParentGraphChannelInterfaceRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := restrictedParentGraphChannelInterfaceSuccessorKindsV0
  obstruction_ids :=
    restrictedParentGraphChannelInterfaceObstructionsV0.map
      restrictedParentGraphChannelInterfaceObstructionId

/-- Short proof-facing status alias. -/
def restrictedParentGraphChannelInterfaceStatusReadoutV0 :
    RestrictedParentGraphChannelInterfaceStatus :=
  restrictedParentGraphChannelInterfaceStatusV0

/-- The restricted parent interface is defined. -/
theorem restricted_parent_graph_channel_interface_defined_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.restricted_interface_defined := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.restricted_interface_defined_supplied

/-- The restricted graph-channel field is exactly actual-error convergence. -/
theorem restricted_parent_graph_channel_field_is_actual_error_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.graph_channel_field_is_actual_error_convergence := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.graph_channel_field_is_actual_error_convergence_supplied

/-- A1A16 satisfies the restricted parent interface. -/
theorem restricted_parent_graph_channel_actual_error_satisfies_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.actual_error_satisfies_restricted_interface := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.actual_error_satisfies_restricted_interface_supplied

/-- The restricted-to-arbitrary bridge condition is stated. -/
theorem restricted_parent_graph_channel_bridge_condition_stated_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.restricted_to_arbitrary_bridge_condition_stated := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.restricted_to_arbitrary_bridge_condition_stated_supplied

/-- The restricted-to-arbitrary parent bridge is not derived by A1A18. -/
theorem restricted_parent_graph_channel_bridge_not_derived_v0 :
    Not
      (restrictedParentGraphChannelInterfaceStatusReadoutV0
        |>.restricted_to_arbitrary_bridge_derived) := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.restricted_to_arbitrary_bridge_not_derived

/-- The arbitrary parent graph-channel interface is not closed by A1A18. -/
theorem restricted_parent_graph_channel_arbitrary_parent_not_closed_v0 :
    Not
      (restrictedParentGraphChannelInterfaceStatusReadoutV0
        |>.arbitrary_parent_interface_closed) := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.arbitrary_parent_interface_not_closed

/-- A2A15A1 remains not ready for review after A1A18. -/
theorem restricted_parent_graph_channel_a2a15a1_not_ready_v0 :
    Not
      (restrictedParentGraphChannelInterfaceStatusReadoutV0
        |>.a2a15a1_ready_for_review) := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.a2a15a1_not_ready_for_review

/-- Phase 2 remains unauthorized after A1A18. -/
theorem restricted_parent_graph_channel_phase2_not_authorized_v0 :
    Not
      (restrictedParentGraphChannelInterfaceStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    restrictedParentGraphChannelInterfaceStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A18 retained blocker id is exposed. -/
theorem restricted_parent_graph_channel_retained_id_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A18RestrictedParentGraphChannelInterfaceRetainedId := by
  rfl

/-- The A1A18 outcome id is exposed. -/
theorem restricted_parent_graph_channel_outcome_id_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0.outcome_id =
      restrictedParentGraphChannelInterfaceRetainedOutcomeId := by
  rfl

/-- The A1A18 obstruction ids are exposed. -/
theorem restricted_parent_graph_channel_obstruction_ids_v0 :
    restrictedParentGraphChannelInterfaceStatusReadoutV0.obstruction_ids =
      restrictedParentGraphChannelInterfaceObstructionsV0.map
        restrictedParentGraphChannelInterfaceObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface
end QFT
end ToeFormal
