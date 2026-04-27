/-
ToeFormal/QFT/ContinuumRestrictedSeparationPrinciple.lean

Restricted separation-principle surface for
PHASE1-BLOCKER-003A2A7.

Scope:
- record the separation condition needed to upgrade weak restricted KG residual
  vanishing into a residual equation
- distinguish admitted-residual separation from the stronger already-defined
  `RestrictedSeparationPrinciple`
- prove the conditional upgrade into the restricted KG route
- prove the anchored trace-vanishing test class cannot separate an off-anchor
  spike residual on a nontrivial point space
- keep concrete functional-analytic separation, nonzero kinetic analysis,
  operator-domain closure, full-field route recovery, and Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumRestrictedKGResidualRoute

namespace ToeFormal
namespace QFT
namespace ContinuumRestrictedSeparationPrinciple

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumMeaningfulTraceModelAttempt
open ContinuumRestrictedTraceVanishingFieldUniverse
open ContinuumRestrictedFirstVariationInterface
open ContinuumRestrictedKGResidualRoute

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the restricted separation-principle slice. -/
def phase1Blocker003A2A7RestrictedSeparationPrincipleRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A7_RESTRICTED_SEPARATION_PRINCIPLE_RETAINED"

/-- Outcome id for this bounded separation-principle slice. -/
def restrictedSeparationPrincipleOutcomeId : String :=
  "RESTRICTED_SEPARATION_PRINCIPLE_CONDITION_RECORDED_" ++
    "ANCHORED_OBSTRUCTION_RETAINED"

/-- Missing objects after the restricted separation-principle attempt. -/
inductive Phase1Blocker003A2A7MissingObject where
  | concreteRestrictedSeparatingTestClass
  | residualAdmissibilityForKGResidual
  | nondegeneratePairingOnRestrictedClass
  | nonzeroScalarKineticOperator
  | greenIdentityForNonzeroOperator
  | operatorDomainClosureForNonzeroOperator
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A7 objects. -/
def phase1Blocker003A2A7MissingObjectId :
    Phase1Blocker003A2A7MissingObject -> String
  | .concreteRestrictedSeparatingTestClass =>
      "003A2A7_CONCRETE_RESTRICTED_SEPARATING_TEST_CLASS_RETAINED"
  | .residualAdmissibilityForKGResidual =>
      "003A2A7_RESIDUAL_ADMISSIBILITY_FOR_KG_RESIDUAL_RETAINED"
  | .nondegeneratePairingOnRestrictedClass =>
      "003A2A7_NONDEGENERATE_PAIRING_ON_RESTRICTED_CLASS_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A7_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .greenIdentityForNonzeroOperator =>
      "003A2A7_GREEN_IDENTITY_FOR_NONZERO_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A7_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"

/-- The explicit remaining objects after this bounded attempt. -/
def phase1Blocker003A2A7MissingObjectsV0 :
    List Phase1Blocker003A2A7MissingObject :=
  [ .concreteRestrictedSeparatingTestClass
  , .residualAdmissibilityForKGResidual
  , .nondegeneratePairingOnRestrictedClass
  , .nonzeroScalarKineticOperator
  , .greenIdentityForNonzeroOperator
  , .operatorDomainClosureForNonzeroOperator
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a7_missing_objects_v0_expected :
    phase1Blocker003A2A7MissingObjectsV0 =
      [ .concreteRestrictedSeparatingTestClass
      , .residualAdmissibilityForKGResidual
      , .nondegeneratePairingOnRestrictedClass
      , .nonzeroScalarKineticOperator
      , .greenIdentityForNonzeroOperator
      , .operatorDomainClosureForNonzeroOperator
      ] := by
  rfl

/--
Restricted residual equation: if the residual belongs to the restricted
residual class, it is zero.  This is weaker than an unconditional full-field
residual equation until residual admissibility is supplied.
-/
def RestrictedResidualEquation {Point : Type}
    (FieldClass : ContinuumField Point -> Prop)
    (residual : ContinuumField Point) : Prop :=
  FieldClass residual -> ResidualEquation residual

/--
Separation only for residuals that are themselves admitted by the restricted
field class.  The stronger `RestrictedSeparationPrinciple` from the previous
interface implies this, but this shape exposes the residual-admissibility debt.
-/
structure AdmittedRestrictedSeparationPrinciple {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop) where
  residual_zero_of_admitted_restricted_pairings_zero :
    forall residual : ContinuumField Point,
      FieldClass residual ->
      RestrictedStationaryFor integral FieldClass residual ->
        ResidualEquation residual

/-- The existing stronger restricted separation principle implies admitted separation. -/
def admittedRestrictedSeparationOfRestrictedSeparation {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (separation : RestrictedSeparationPrinciple integral FieldClass) :
    AdmittedRestrictedSeparationPrinciple integral FieldClass where
  residual_zero_of_admitted_restricted_pairings_zero := by
    intro residual _hResidual hWeak
    exact separation.residual_zero_of_all_restricted_pairings_zero residual hWeak

/-- Weak KG residual vanishing upgrades under admitted restricted separation. -/
theorem admitted_restricted_separation_upgrades_weak_kg_residual
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (separation : AdmittedRestrictedSeparationPrinciple integral FieldClass)
    (hResidual : FieldClass (Residual operator massSq phi))
    (hWeak :
      RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact separation.residual_zero_of_admitted_restricted_pairings_zero
    (Residual operator massSq phi) hResidual
    (by
      intro eta heta
      exact hWeak eta heta)

/-- Weak KG residual vanishing gives a restricted residual equation. -/
theorem weak_kg_residual_gives_restricted_residual_equation
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (separation : AdmittedRestrictedSeparationPrinciple integral FieldClass)
    (hWeak :
      RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi) :
    RestrictedResidualEquation FieldClass (Residual operator massSq phi) := by
  intro hResidual
  exact admitted_restricted_separation_upgrades_weak_kg_residual
    integral operator massSq FieldClass phi separation hResidual hWeak

/-- Restricted stationarity plus admitted separation gives restricted residual zero. -/
theorem restricted_stationarity_plus_admitted_separation_gives_restricted_residual
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (separation : AdmittedRestrictedSeparationPrinciple integral FieldClass)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    RestrictedResidualEquation FieldClass (Residual operator massSq phi) := by
  exact weak_kg_residual_gives_restricted_residual_equation
    integral operator massSq FieldClass phi separation
    (restricted_stationarity_implies_restricted_kg_residual_weak
      integral operator massSq FieldClass phi hStationary)

/-- Off-anchor spike field used to test the anchored restricted class. -/
def anchoredOffAnchorSpike {Point : Type} [DecidableEq Point]
    (q : Point) : ContinuumField Point :=
  fun p => if p = q then 1 else 0

/-- The off-anchor spike vanishes at the anchor. -/
theorem anchored_off_anchor_spike_at_anchor_zero {Point : Type}
    [Inhabited Point] [DecidableEq Point]
    {q : Point} (hq : q ≠ (default : Point)) :
    anchoredOffAnchorSpike q (default : Point) = 0 := by
  have hDefault : (default : Point) ≠ q := by
    intro h
    exact hq h.symm
  simp [anchoredOffAnchorSpike, hDefault]

/-- The off-anchor spike belongs to the anchored trace-vanishing field class. -/
theorem anchored_off_anchor_spike_in_restricted_class {Point : Type}
    [Inhabited Point] [DecidableEq Point]
    {q : Point} (hq : q ≠ (default : Point)) :
    AnchoredTraceVanishingFieldClass (anchoredOffAnchorSpike q) := by
  have hZero :=
    anchored_off_anchor_spike_at_anchor_zero (Point := Point) hq
  change
    (anchoredTraceZeroOperatorBoundaryProblem Point).trace.leftTrace
          (anchoredOffAnchorSpike q) = 0 ∧
      (anchoredTraceZeroOperatorBoundaryProblem Point).trace.rightTrace
          (anchoredOffAnchorSpike q) = 0
  constructor
  · simpa [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace] using hZero
  · simpa [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace] using hZero

/-- The off-anchor spike is not the zero field. -/
theorem anchored_off_anchor_spike_nonzero {Point : Type}
    [DecidableEq Point] (q : Point) :
    anchoredOffAnchorSpike q ≠ (0 : ContinuumField Point) := by
  intro h
  have hAtQ := congrFun h q
  simp [anchoredOffAnchorSpike] at hAtQ

/-- Admitted anchored tests cannot see the off-anchor spike. -/
theorem anchored_off_anchor_spike_weakly_invisible {Point : Type}
    [Inhabited Point] [DecidableEq Point]
    {q : Point} (_hq : q ≠ (default : Point)) :
    RestrictedStationaryFor
      (@anchoredContinuumIntegral Point _)
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
      (anchoredOffAnchorSpike q) := by
  intro eta heta
  have hLeft :
      (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).leftTrace eta = 0 := by
    exact anchored_trace_vanishing_class_left_trace_zero eta heta
  have hEtaAnchor : eta (default : Point) = 0 := by
    simpa [anchoredMeaningfulTwoSidedBoundaryTrace] using hLeft
  simp [ContinuumPair, anchoredContinuumIntegral, hEtaAnchor]

/--
The anchored trace-vanishing class cannot provide admitted restricted
separation on a point space with an off-anchor point.
-/
theorem anchored_trace_vanishing_no_admitted_restricted_separation
    {Point : Type} [Inhabited Point]
    {q : Point} (hq : q ≠ (default : Point)) :
    Not (AdmittedRestrictedSeparationPrinciple
      (@anchoredContinuumIntegral Point _)
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass) := by
  classical
  intro separation
  have hResidual :
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
        (anchoredOffAnchorSpike q) := by
    exact anchored_off_anchor_spike_in_restricted_class (Point := Point) hq
  have hWeak :
      RestrictedStationaryFor
        (@anchoredContinuumIntegral Point _)
        (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
        (anchoredOffAnchorSpike q) := by
    exact anchored_off_anchor_spike_weakly_invisible (Point := Point) hq
  have hZero :=
    separation.residual_zero_of_admitted_restricted_pairings_zero
      (anchoredOffAnchorSpike q) hResidual hWeak
  exact anchored_off_anchor_spike_nonzero q hZero

/-- Status readout for this bounded restricted separation attempt. -/
structure RestrictedSeparationPrincipleAttemptStatus where
  restricted_residual_equation_defined : Prop
  admitted_separation_principle_defined : Prop
  weak_kg_upgrade_recorded : Prop
  strong_principle_implies_admitted_principle : Prop
  anchored_obstruction_recorded : Prop
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
def restrictedSeparationPrincipleAttemptStatusV0 :
    RestrictedSeparationPrincipleAttemptStatus where
  restricted_residual_equation_defined := True
  admitted_separation_principle_defined := True
  weak_kg_upgrade_recorded := True
  strong_principle_implies_admitted_principle := True
  anchored_obstruction_recorded := True
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
    phase1Blocker003A2A6RestrictedKGResidualRouteRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A7RestrictedSeparationPrincipleRetainedId
  outcome_id := restrictedSeparationPrincipleOutcomeId

/-- Short local status alias. -/
def restrictedSeparationStatusV0 :
    RestrictedSeparationPrincipleAttemptStatus :=
  restrictedSeparationPrincipleAttemptStatusV0

/-- The restricted residual equation is defined. -/
theorem restricted_separation_residual_equation_defined_v0 :
    restrictedSeparationStatusV0.restricted_residual_equation_defined := by
  trivial

/-- The admitted restricted separation principle is defined. -/
theorem restricted_separation_admitted_principle_defined_v0 :
    restrictedSeparationStatusV0.admitted_separation_principle_defined := by
  trivial

/-- The weak KG upgrade is recorded. -/
theorem restricted_separation_weak_kg_upgrade_recorded_v0 :
    restrictedSeparationStatusV0.weak_kg_upgrade_recorded := by
  trivial

/-- The stronger restricted principle implies the admitted principle. -/
theorem restricted_separation_strong_implies_admitted_v0 :
    restrictedSeparationStatusV0.strong_principle_implies_admitted_principle := by
  trivial

/-- The anchored obstruction is recorded. -/
theorem restricted_separation_anchored_obstruction_recorded_v0 :
    restrictedSeparationStatusV0.anchored_obstruction_recorded := by
  trivial

/-- No concrete restricted separation principle is constructed in this slice. -/
theorem restricted_separation_concrete_not_constructed_v0 :
    Not restrictedSeparationStatusV0.concrete_restricted_separation_constructed := by
  exact restrictedSeparationStatusV0.concrete_restricted_separation_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem restricted_separation_nonzero_operator_green_not_closed_v0 :
    Not restrictedSeparationStatusV0.nonzero_operator_green_identity_closed := by
  exact restrictedSeparationStatusV0.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem restricted_separation_parent_retained_id_v0 :
    restrictedSeparationStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A6RestrictedKGResidualRouteRetainedId := by
  simp [restrictedSeparationStatusV0,
    restrictedSeparationPrincipleAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem restricted_separation_retained_id_v0 :
    restrictedSeparationStatusV0.retained_blocker_id =
      phase1Blocker003A2A7RestrictedSeparationPrincipleRetainedId := by
  simp [restrictedSeparationStatusV0,
    restrictedSeparationPrincipleAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem restricted_separation_outcome_id_v0 :
    restrictedSeparationStatusV0.outcome_id =
      restrictedSeparationPrincipleOutcomeId := by
  simp [restrictedSeparationStatusV0,
    restrictedSeparationPrincipleAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded attempt. -/
theorem restricted_separation_phase2_not_authorized_v0 :
    Not restrictedSeparationStatusV0.phase2Authorized := by
  exact restrictedSeparationStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained separation-principle route. -/
def phase1Blocker003A2A7RestrictedSeparationPrincipleV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a7_restricted_separation_v0_phase2_not_authorized :
    Not phase1Blocker003A2A7RestrictedSeparationPrincipleV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumRestrictedSeparationPrinciple
end QFT
end ToeFormal
