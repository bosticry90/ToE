/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianParentInterfaceEquivalenceBridge.lean

A1A19 restricted-to-arbitrary parent interface bridge after the A1A18
restricted parent graph-channel interface.

Scope:
- define the exact bridge condition between the restricted parent graph-channel
  proposition and the arbitrary parent contract graph-channel proposition
- prove that proposition equality or theorem-equivalence supplies the A1A18
  restricted-to-arbitrary bridge
- prove that A1A16 actual graph-error evidence fills the arbitrary parent
  graph-channel field when that equality/equivalence is supplied
- record that the equality/equivalence is not derived here, so A2A15A1
  closure and Phase 2 authorization remain out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianParentInterfaceEquivalenceBridge

open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
open ContinuumSpatialGraphLaplacianRestrictedParentGraphChannelInterface

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A19 parent-interface equivalence bridge. -/
def a1a19ParentInterfaceEquivalenceBridgeSurfaceId : String :=
  "A2A15A1A19_PARENT_INTERFACE_EQUIVALENCE_BRIDGE"

/-- Retained blocker when parent-interface equivalence is not derived. -/
def phase1Blocker003A2A15A1A19ParentInterfaceEquivalenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A19_PARENT_INTERFACE_" ++
    "EQUIVALENCE_RETAINED"

/-- Outcome id for the retained A1A19 equivalence slice. -/
def parentInterfaceEquivalenceRetainedOutcomeId : String :=
  "PARENT_INTERFACE_EQUIVALENCE_RETAINED"

/--
Theorem-equivalence bridge condition between a restricted parent interface and
an arbitrary parent contract.

This is stronger than the A1A18 implication-shaped bridge because it states
that both graph-channel propositions express the same theorem-facing claim.
-/
def ParentGraphChannelTheoremEquivalence
    {ContinuumPoint : Type}
    {f : Real -> Real}
    {x C : Real}
    (_target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract _target)
    (restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C) : Prop :=
  restrictedInterface.graph_laplacian_action_to_continuum_laplacian ↔
    parentContract.graph_laplacian_action_to_continuum_laplacian

/--
Proposition-equality bridge condition between a restricted parent interface and
an arbitrary parent contract.

Definitional equality is a special case of this condition, discharged by `rfl`
when the parent field is definitionally the restricted graph-channel field.
-/
def ParentGraphChannelPropositionEquality
    {ContinuumPoint : Type}
    {f : Real -> Real}
    {x C : Real}
    (_target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract _target)
    (restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C) : Prop :=
  parentContract.graph_laplacian_action_to_continuum_laplacian =
    restrictedInterface.graph_laplacian_action_to_continuum_laplacian

/-- Equality of graph-channel propositions implies theorem-equivalence. -/
theorem parent_graph_channel_equivalence_of_proposition_equality_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C}
    (hEq :
      ParentGraphChannelPropositionEquality
        target parentContract restrictedInterface) :
    ParentGraphChannelTheoremEquivalence
      target parentContract restrictedInterface := by
  rw [ParentGraphChannelPropositionEquality] at hEq
  rw [ParentGraphChannelTheoremEquivalence]
  rw [hEq]

/-- Theorem-equivalence manufactures the A1A18 restricted-to-arbitrary bridge. -/
def restrictedToArbitraryParentBridgeOfTheoremEquivalence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C}
    (hEquiv :
      ParentGraphChannelTheoremEquivalence
        target parentContract restrictedInterface) :
    RestrictedToArbitraryParentGraphChannelBridge
      target parentContract restrictedInterface where
  restricted_graph_channel_supplies_parent := by
    intro hRestricted
    exact hEquiv.mp hRestricted

/-- Proposition equality manufactures the A1A18 restricted-to-arbitrary bridge. -/
def restrictedToArbitraryParentBridgeOfPropositionEquality
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {restrictedInterface :
      RestrictedParentGraphChannelInterface (f := f) x C}
    (hEq :
      ParentGraphChannelPropositionEquality
        target parentContract restrictedInterface) :
    RestrictedToArbitraryParentGraphChannelBridge
      target parentContract restrictedInterface :=
  restrictedToArbitraryParentBridgeOfTheoremEquivalence
    (parent_graph_channel_equivalence_of_proposition_equality_v0
      (target := target)
      (parentContract := parentContract)
      (restrictedInterface := restrictedInterface)
      hEq)

/--
The actual-error version of the equivalence bridge condition.

For the canonical A1A18 restricted interface, the restricted proposition is
definitionally the A1A16 actual graph-error stencil-limit proposition.
-/
def ParentGraphChannelActualErrorTheoremEquivalence
    {ContinuumPoint : Type}
    {f : Real -> Real}
    {x C : Real}
    (_target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract _target)
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) : Prop :=
  actualGraphErrorRestrictedParentGraphChannelField evidenceOnly ↔
    parentContract.graph_laplacian_action_to_continuum_laplacian

/-- Equality version of the actual-error parent graph-channel bridge condition. -/
def ParentGraphChannelActualErrorPropositionEquality
    {ContinuumPoint : Type}
    {f : Real -> Real}
    {x C : Real}
    (_target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract _target)
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) : Prop :=
  parentContract.graph_laplacian_action_to_continuum_laplacian =
    actualGraphErrorRestrictedParentGraphChannelField evidenceOnly

/-- Actual-error theorem-equivalence is the canonical restricted-interface equivalence. -/
theorem parent_graph_channel_restricted_equivalence_of_actual_error_equivalence_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C}
    (hEquiv :
      ParentGraphChannelActualErrorTheoremEquivalence
        target parentContract evidenceOnly) :
    ParentGraphChannelTheoremEquivalence
      target
      parentContract
      (restrictedParentGraphChannelInterfaceOfActualGraphError
        evidenceOnly) := by
  rw [ParentGraphChannelTheoremEquivalence]
  exact hEquiv

/-- Actual-error proposition equality implies the canonical theorem-equivalence. -/
theorem parent_graph_channel_actual_error_equivalence_of_equality_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    {evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C}
    (hEq :
      ParentGraphChannelActualErrorPropositionEquality
        target parentContract evidenceOnly) :
    ParentGraphChannelActualErrorTheoremEquivalence
      target parentContract evidenceOnly := by
  rw [ParentGraphChannelActualErrorPropositionEquality] at hEq
  rw [ParentGraphChannelActualErrorTheoremEquivalence]
  rw [hEq]

/-- If the parent graph-channel field is theorem-equivalent, A1A18 supplies it. -/
theorem actual_graph_error_satisfies_parent_given_interface_equivalence_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C)
    (hEquiv :
      ParentGraphChannelActualErrorTheoremEquivalence
        target parentContract evidenceOnly) :
    parentContract.graph_laplacian_action_to_continuum_laplacian := by
  exact
    actual_graph_error_satisfies_parent_given_restricted_bridge_v0
      evidenceOnly
      (restrictedToArbitraryParentBridgeOfTheoremEquivalence
        (parent_graph_channel_restricted_equivalence_of_actual_error_equivalence_v0
          (target := target)
          (parentContract := parentContract)
          (evidenceOnly := evidenceOnly)
          hEquiv))

/-- If the parent graph-channel field is proposition-equal, A1A18 supplies it. -/
theorem actual_graph_error_satisfies_parent_given_interface_equality_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {parentContract : AnalyticIntervalLiftConvergenceContract target}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C)
    (hEq :
      ParentGraphChannelActualErrorPropositionEquality
        target parentContract evidenceOnly) :
    parentContract.graph_laplacian_action_to_continuum_laplacian := by
  exact
    actual_graph_error_satisfies_parent_given_interface_equivalence_v0
      evidenceOnly
      (parent_graph_channel_actual_error_equivalence_of_equality_v0
        (target := target)
        (parentContract := parentContract)
        (evidenceOnly := evidenceOnly)
        hEq)

/-- Remaining objects after the A1A19 equivalence bridge slice. -/
inductive ParentInterfaceEquivalenceBridgeObstruction where
  | noParentInterfaceEquivalence
  | noDefinitionalOrTheoremEquivalence
  | noContinuumLaplacianSemanticClosure
  | noOperatorDomainClosureFromActualError
  | noParentGraphRelation
  | noA2A15A1AssemblyReview
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A19 objects. -/
def parentInterfaceEquivalenceBridgeObstructionId :
    ParentInterfaceEquivalenceBridgeObstruction -> String
  | .noParentInterfaceEquivalence =>
      "A1A19_OBSTRUCTION_NO_PARENT_INTERFACE_EQUIVALENCE"
  | .noDefinitionalOrTheoremEquivalence =>
      "A1A19_OBSTRUCTION_NO_DEFINITIONAL_OR_THEOREM_EQUIVALENCE"
  | .noContinuumLaplacianSemanticClosure =>
      "A1A19_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTIC_CLOSURE"
  | .noOperatorDomainClosureFromActualError =>
      "A1A19_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FROM_ACTUAL_ERROR"
  | .noParentGraphRelation =>
      "A1A19_OBSTRUCTION_NO_PARENT_GRAPH_RELATION"
  | .noA2A15A1AssemblyReview =>
      "A1A19_OBSTRUCTION_NO_A2A15A1_ASSEMBLY_REVIEW"
  | .noPhase2Authorization =>
      "A1A19_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A19 bridge-equivalence slice. -/
def parentInterfaceEquivalenceBridgeObstructionsV0 :
    List ParentInterfaceEquivalenceBridgeObstruction :=
  [ .noParentInterfaceEquivalence
  , .noDefinitionalOrTheoremEquivalence
  , .noContinuumLaplacianSemanticClosure
  , .noOperatorDomainClosureFromActualError
  , .noParentGraphRelation
  , .noA2A15A1AssemblyReview
  , .noPhase2Authorization
  ]

/-- The A1A19 obstruction list is stable and explicit. -/
theorem parent_interface_equivalence_bridge_obstructions_v0_expected :
    parentInterfaceEquivalenceBridgeObstructionsV0 =
      [ .noParentInterfaceEquivalence
      , .noDefinitionalOrTheoremEquivalence
      , .noContinuumLaplacianSemanticClosure
      , .noOperatorDomainClosureFromActualError
      , .noParentGraphRelation
      , .noA2A15A1AssemblyReview
      , .noPhase2Authorization
      ] := by
  rfl

/-- This successor proves conditional channel transport and records obstruction. -/
def parentInterfaceEquivalenceBridgeSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A19 successor kind records proof progress plus retained obstruction. -/
theorem parent_interface_equivalence_bridge_successor_kinds_v0_expected :
    parentInterfaceEquivalenceBridgeSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A19 parent-interface equivalence bridge. -/
structure ParentInterfaceEquivalenceBridgeStatus where
  bridge_surface_defined : Prop
  bridge_surface_defined_supplied : bridge_surface_defined
  exact_bridge_condition_defined : Prop
  exact_bridge_condition_defined_supplied : exact_bridge_condition_defined
  equality_supplies_bridge : Prop
  equality_supplies_bridge_supplied : equality_supplies_bridge
  theorem_equivalence_supplies_bridge : Prop
  theorem_equivalence_supplies_bridge_supplied :
    theorem_equivalence_supplies_bridge
  actual_error_supplies_parent_given_equivalence : Prop
  actual_error_supplies_parent_given_equivalence_supplied :
    actual_error_supplies_parent_given_equivalence
  parent_interface_equivalence_derived : Prop
  parent_interface_equivalence_not_derived :
    Not parent_interface_equivalence_derived
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
Current A1A19 result: equality/equivalence would close the parent graph field
from A1A18, but the equivalence itself remains retained.
-/
def parentInterfaceEquivalenceBridgeStatusV0 :
    ParentInterfaceEquivalenceBridgeStatus where
  bridge_surface_defined := True
  bridge_surface_defined_supplied := True.intro
  exact_bridge_condition_defined := True
  exact_bridge_condition_defined_supplied := True.intro
  equality_supplies_bridge := True
  equality_supplies_bridge_supplied := True.intro
  theorem_equivalence_supplies_bridge := True
  theorem_equivalence_supplies_bridge_supplied := True.intro
  actual_error_supplies_parent_given_equivalence := True
  actual_error_supplies_parent_given_equivalence_supplied := True.intro
  parent_interface_equivalence_derived := False
  parent_interface_equivalence_not_derived := by
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
  surface_id := a1a19ParentInterfaceEquivalenceBridgeSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A18RestrictedParentGraphChannelInterfaceRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A19ParentInterfaceEquivalenceRetainedId
  outcome_id := parentInterfaceEquivalenceRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := parentInterfaceEquivalenceBridgeSuccessorKindsV0
  obstruction_ids :=
    parentInterfaceEquivalenceBridgeObstructionsV0.map
      parentInterfaceEquivalenceBridgeObstructionId

/-- Short proof-facing status alias. -/
def parentInterfaceEquivalenceBridgeStatusReadoutV0 :
    ParentInterfaceEquivalenceBridgeStatus :=
  parentInterfaceEquivalenceBridgeStatusV0

/-- The A1A19 bridge surface is recorded. -/
theorem parent_interface_equivalence_bridge_surface_defined_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.bridge_surface_defined := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.bridge_surface_defined_supplied

/-- The exact equivalence/equality bridge condition is recorded. -/
theorem parent_interface_equivalence_bridge_condition_defined_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.exact_bridge_condition_defined := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.exact_bridge_condition_defined_supplied

/-- Proposition equality supplies the restricted-to-arbitrary bridge. -/
theorem parent_interface_equivalence_bridge_equality_supplies_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.equality_supplies_bridge := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.equality_supplies_bridge_supplied

/-- Theorem-equivalence supplies the restricted-to-arbitrary bridge. -/
theorem parent_interface_equivalence_bridge_theorem_equivalence_supplies_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.theorem_equivalence_supplies_bridge := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.theorem_equivalence_supplies_bridge_supplied

/-- A1A16 actual-error evidence supplies the parent field if equivalence is supplied. -/
theorem parent_interface_equivalence_actual_error_supplies_parent_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.actual_error_supplies_parent_given_equivalence := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.actual_error_supplies_parent_given_equivalence_supplied

/-- The parent-interface equivalence is not derived by A1A19. -/
theorem parent_interface_equivalence_not_derived_v0 :
    Not
      (parentInterfaceEquivalenceBridgeStatusReadoutV0
        |>.parent_interface_equivalence_derived) := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.parent_interface_equivalence_not_derived

/-- The arbitrary parent graph-channel interface is not closed by A1A19 alone. -/
theorem parent_interface_equivalence_arbitrary_parent_not_closed_v0 :
    Not
      (parentInterfaceEquivalenceBridgeStatusReadoutV0
        |>.arbitrary_parent_interface_closed) := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.arbitrary_parent_interface_not_closed

/-- A2A15A1 remains not ready for review after A1A19. -/
theorem parent_interface_equivalence_a2a15a1_not_ready_v0 :
    Not
      (parentInterfaceEquivalenceBridgeStatusReadoutV0
        |>.a2a15a1_ready_for_review) := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.a2a15a1_not_ready_for_review

/-- Phase 2 remains unauthorized after A1A19. -/
theorem parent_interface_equivalence_phase2_not_authorized_v0 :
    Not
      (parentInterfaceEquivalenceBridgeStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    parentInterfaceEquivalenceBridgeStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A19 retained blocker id is exposed. -/
theorem parent_interface_equivalence_retained_id_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A19ParentInterfaceEquivalenceRetainedId := by
  rfl

/-- The A1A19 outcome id is exposed. -/
theorem parent_interface_equivalence_outcome_id_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0.outcome_id =
      parentInterfaceEquivalenceRetainedOutcomeId := by
  rfl

/-- The A1A19 obstruction ids are exposed. -/
theorem parent_interface_equivalence_obstruction_ids_v0 :
    parentInterfaceEquivalenceBridgeStatusReadoutV0.obstruction_ids =
      parentInterfaceEquivalenceBridgeObstructionsV0.map
        parentInterfaceEquivalenceBridgeObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianParentInterfaceEquivalenceBridge
end QFT
end ToeFormal
