/-
ToeFormal/QFT/ContinuumRestrictedKGResidualRoute.lean

Restricted KG/residual theorem route for
PHASE1-BLOCKER-003A2A6.

Scope:
- define the restricted KG residual conclusion over admitted test fields
- prove restricted first-variation stationarity gives residual pairing zero
  against admitted variations
- record the conditional upgrade supplied by a restricted separation principle
- reuse the restricted action-shift expansion from the restricted
  first-variation interface
- instantiate the weak restricted route for the anchored zero-field witness
- keep full-field continuum closure, nonzero kinetic analysis, concrete
  restricted separation, operator-domain closure, and Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumRestrictedFirstVariationInterface

namespace ToeFormal
namespace QFT
namespace ContinuumRestrictedKGResidualRoute

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumRestrictedTraceVanishingFieldUniverse
open ContinuumRestrictedClosedBoundaryUniverseAPI
open ContinuumRestrictedFirstVariationInterface

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the restricted KG residual route slice. -/
def phase1Blocker003A2A6RestrictedKGResidualRouteRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A6_RESTRICTED_KG_RESIDUAL_ROUTE_RETAINED"

/-- Outcome id for this bounded restricted route. -/
def restrictedKGResidualRouteOutcomeId : String :=
  "RESTRICTED_KG_RESIDUAL_ROUTE_WEAK_THEOREM_DISCHARGED_" ++
    "SEPARATION_RETAINED"

/-- Missing objects after the restricted KG residual route slice. -/
inductive Phase1Blocker003A2A6MissingObject where
  | concreteRestrictedSeparationPrinciple
  | nonzeroScalarKineticOperator
  | greenIdentityForNonzeroOperator
  | operatorDomainClosureForNonzeroOperator
  | nontrivialRestrictedStationaryPoint
  | fullFieldContinuumRouteBridge
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A6 objects. -/
def phase1Blocker003A2A6MissingObjectId :
    Phase1Blocker003A2A6MissingObject -> String
  | .concreteRestrictedSeparationPrinciple =>
      "003A2A6_CONCRETE_RESTRICTED_SEPARATION_PRINCIPLE_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A6_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .greenIdentityForNonzeroOperator =>
      "003A2A6_GREEN_IDENTITY_FOR_NONZERO_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A6_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"
  | .nontrivialRestrictedStationaryPoint =>
      "003A2A6_NONTRIVIAL_RESTRICTED_STATIONARY_POINT_RETAINED"
  | .fullFieldContinuumRouteBridge =>
      "003A2A6_FULL_FIELD_CONTINUUM_ROUTE_BRIDGE_RETAINED"

/-- The explicit remaining objects after this bounded attempt. -/
def phase1Blocker003A2A6MissingObjectsV0 :
    List Phase1Blocker003A2A6MissingObject :=
  [ .concreteRestrictedSeparationPrinciple
  , .nonzeroScalarKineticOperator
  , .greenIdentityForNonzeroOperator
  , .operatorDomainClosureForNonzeroOperator
  , .nontrivialRestrictedStationaryPoint
  , .fullFieldContinuumRouteBridge
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a6_missing_objects_v0_expected :
    phase1Blocker003A2A6MissingObjectsV0 =
      [ .concreteRestrictedSeparationPrinciple
      , .nonzeroScalarKineticOperator
      , .greenIdentityForNonzeroOperator
      , .operatorDomainClosureForNonzeroOperator
      , .nontrivialRestrictedStationaryPoint
      , .fullFieldContinuumRouteBridge
      ] := by
  rfl

/-- Stationarity of the first variation against admitted variations only. -/
def RestrictedFirstVariationStationaryFor {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point) : Prop :=
  forall eta : ContinuumField Point,
    FieldClass eta -> FirstVariation integral operator massSq phi eta = 0

/-- Weak restricted KG residual equation: zero against admitted tests. -/
def RestrictedKGResidualWeakEquation {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point) : Prop :=
  forall eta : ContinuumField Point,
    FieldClass eta ->
      ContinuumPair integral eta (Residual operator massSq phi) = 0

/--
Restricted KG residual conclusion.  This is explicitly weaker than the old
full-field residual equation: it records only admitted-field testing.
-/
structure RestrictedKGResidualConclusion {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point) where
  phi_admitted : FieldClass phi
  residual_zero_on_admitted_tests :
    RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi

/-- Restricted stationarity is exactly weak restricted KG residual vanishing. -/
theorem restricted_stationarity_implies_restricted_kg_residual_weak
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi := by
  intro eta heta
  simpa [RestrictedFirstVariationStationaryFor,
    RestrictedKGResidualWeakEquation, FirstVariation] using
      hStationary eta heta

/-- Restricted stationarity gives the restricted KG conclusion for admitted `phi`. -/
theorem restricted_stationarity_gives_restricted_kg_residual_conclusion
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (hPhi : FieldClass phi)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    RestrictedKGResidualConclusion integral operator massSq FieldClass phi where
  phi_admitted := hPhi
  residual_zero_on_admitted_tests :=
    restricted_stationarity_implies_restricted_kg_residual_weak
      integral operator massSq FieldClass phi hStationary

/--
A supplied restricted separation principle upgrades the weak restricted
conclusion to the old residual equation.  This is conditional evidence only.
-/
theorem restricted_kg_residual_weak_upgrades_under_supplied_separation
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (separation : RestrictedSeparationPrinciple integral FieldClass)
    (hWeak :
      RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact separation.residual_zero_of_all_restricted_pairings_zero
    (Residual operator massSq phi) hWeak

/-- Restricted stationarity plus supplied separation gives conditional residual zero. -/
theorem restricted_stationarity_plus_separation_implies_residual_zero
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (separation : RestrictedSeparationPrinciple integral FieldClass)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact restricted_kg_residual_weak_upgrades_under_supplied_separation
    integral operator massSq FieldClass phi separation
    (restricted_stationarity_implies_restricted_kg_residual_weak
      integral operator massSq FieldClass phi hStationary)

/-- Reuse of the restricted first-variation action-shift theorem. -/
theorem restricted_kg_route_reuses_action_shift_expansion
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (obligation : RestrictedFirstVariationObligations integral operator)
    (massSq : Real)
    (phi eta : ContinuumField Point)
    (hPhi : obligation.restricted_boundary_model.FieldClass phi)
    (hEta : obligation.restricted_boundary_model.FieldClass eta) :
    HasAlgebraicDerivativeAtZero
      (fun eps =>
        ContinuumFirstVariation.Action integral operator massSq
          (VariationFamily phi eta eps))
      (ContinuumFirstVariation.Action integral operator massSq phi)
      (FirstVariation integral operator massSq phi eta) := by
  exact restricted_action_has_algebraic_derivative_at_zero
    integral operator obligation massSq phi eta hPhi hEta

/-- The zero field is restricted stationary for the anchored zero-operator route. -/
theorem anchored_zero_field_restricted_stationary
    {Point : Type} [Inhabited Point]
    (massSq : Real) :
    RestrictedFirstVariationStationaryFor
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point)
      massSq
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
      (@zeroField Point) := by
  intro eta heta
  simp [FirstVariation, Residual, zeroKineticOperator, fieldAdd, fieldSMul,
    zeroField, ContinuumPair, anchoredContinuumIntegral]

/-- The anchored zero field satisfies the weak restricted KG residual equation. -/
theorem anchored_zero_field_restricted_kg_residual_weak
    {Point : Type} [Inhabited Point]
    (massSq : Real) :
    RestrictedKGResidualWeakEquation
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point)
      massSq
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
      (@zeroField Point) := by
  exact restricted_stationarity_implies_restricted_kg_residual_weak
    (@anchoredContinuumIntegral Point _)
    (@zeroKineticOperator Point)
    massSq
    (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
    (@zeroField Point)
    (anchored_zero_field_restricted_stationary massSq)

/-- The anchored zero field gives a concrete weak restricted KG conclusion. -/
theorem anchored_zero_field_restricted_kg_residual_conclusion
    {Point : Type} [Inhabited Point]
    (massSq : Real) :
    RestrictedKGResidualConclusion
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point)
      massSq
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
      (@zeroField Point) := by
  exact restricted_stationarity_gives_restricted_kg_residual_conclusion
    (@anchoredContinuumIntegral Point _)
    (@zeroKineticOperator Point)
    massSq
    (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
    (@zeroField Point)
    zero_field_in_anchored_trace_vanishing_class
    (anchored_zero_field_restricted_stationary massSq)

/-- Status readout for this bounded restricted KG route attempt. -/
structure RestrictedKGResidualRouteAttemptStatus where
  restricted_kg_conclusion_defined : Prop
  weak_restricted_kg_route_discharged : Prop
  action_shift_route_reused : Prop
  conditional_separation_upgrade_recorded : Prop
  anchored_zero_field_witness_recorded : Prop
  concrete_restricted_separation_constructed : Prop
  concrete_restricted_separation_not_constructed :
    Not concrete_restricted_separation_constructed
  nonzero_operator_green_identity_closed : Prop
  nonzero_operator_green_identity_not_closed :
    Not nonzero_operator_green_identity_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this attempt. -/
def restrictedKGResidualRouteAttemptStatusV0 :
    RestrictedKGResidualRouteAttemptStatus where
  restricted_kg_conclusion_defined := True
  weak_restricted_kg_route_discharged := True
  action_shift_route_reused := True
  conditional_separation_upgrade_recorded := True
  anchored_zero_field_witness_recorded := True
  concrete_restricted_separation_constructed := False
  concrete_restricted_separation_not_constructed := by
    intro h
    exact h
  nonzero_operator_green_identity_closed := False
  nonzero_operator_green_identity_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A5RestrictedFirstVariationInterfaceRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A6RestrictedKGResidualRouteRetainedId
  outcome_id := restrictedKGResidualRouteOutcomeId

/-- Short local status alias. -/
def restrictedKGResidualStatusV0 :
    RestrictedKGResidualRouteAttemptStatus :=
  restrictedKGResidualRouteAttemptStatusV0

/-- The restricted KG conclusion is defined. -/
theorem restricted_kg_conclusion_defined_v0 :
    restrictedKGResidualStatusV0.restricted_kg_conclusion_defined := by
  trivial

/-- The weak restricted KG route is discharged. -/
theorem restricted_kg_weak_route_discharged_v0 :
    restrictedKGResidualStatusV0.weak_restricted_kg_route_discharged := by
  trivial

/-- The restricted action-shift route is reused. -/
theorem restricted_kg_action_shift_reused_v0 :
    restrictedKGResidualStatusV0.action_shift_route_reused := by
  trivial

/-- The conditional restricted-separation upgrade is recorded. -/
theorem restricted_kg_conditional_separation_upgrade_recorded_v0 :
    restrictedKGResidualStatusV0.conditional_separation_upgrade_recorded := by
  trivial

/-- The anchored zero-field weak witness is recorded. -/
theorem restricted_kg_anchored_zero_field_witness_recorded_v0 :
    restrictedKGResidualStatusV0.anchored_zero_field_witness_recorded := by
  trivial

/-- No concrete restricted separation principle is constructed in this slice. -/
theorem restricted_kg_concrete_separation_not_constructed_v0 :
    Not restrictedKGResidualStatusV0.concrete_restricted_separation_constructed := by
  exact restrictedKGResidualStatusV0.concrete_restricted_separation_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem restricted_kg_nonzero_operator_green_not_closed_v0 :
    Not restrictedKGResidualStatusV0.nonzero_operator_green_identity_closed := by
  exact restrictedKGResidualStatusV0.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem restricted_kg_parent_retained_id_v0 :
    restrictedKGResidualStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A5RestrictedFirstVariationInterfaceRetainedId := by
  simp [restrictedKGResidualStatusV0, restrictedKGResidualRouteAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem restricted_kg_retained_id_v0 :
    restrictedKGResidualStatusV0.retained_blocker_id =
      phase1Blocker003A2A6RestrictedKGResidualRouteRetainedId := by
  simp [restrictedKGResidualStatusV0, restrictedKGResidualRouteAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem restricted_kg_outcome_id_v0 :
    restrictedKGResidualStatusV0.outcome_id =
      restrictedKGResidualRouteOutcomeId := by
  simp [restrictedKGResidualStatusV0, restrictedKGResidualRouteAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded route. -/
theorem restricted_kg_phase2_not_authorized_v0 :
    Not restrictedKGResidualStatusV0.phase2Authorized := by
  exact restrictedKGResidualStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained KG residual route. -/
def phase1Blocker003A2A6RestrictedKGResidualRouteV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a6_restricted_kg_v0_phase2_not_authorized :
    Not phase1Blocker003A2A6RestrictedKGResidualRouteV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumRestrictedKGResidualRoute
end QFT
end ToeFormal
