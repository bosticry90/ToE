/-
ToeFormal/QFT/ContinuumResidualAdmissibility.lean

Residual-admissibility surface for PHASE1-BLOCKER-003A2A9.

Scope:
- define when KG residuals of admitted fields stay admitted by a restricted
  field class
- split that condition into operator-image, mass-term, and addition-closure
  evidence
- prove that supplied residual admissibility closes the residual-admission gap
  in the A2A8 separating test-class route
- prove the zero-operator anchored restricted route is residually admissible
- keep nonzero scalar kinetic domain closure, nondegenerate pairing,
  concrete separating test-class construction, full-field route recovery, and
  Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumSeparatingTestClassCandidate

namespace ToeFormal
namespace QFT
namespace ContinuumResidualAdmissibility

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumGreenIdentityAttempt
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumMeaningfulTraceModelAttempt
open ContinuumRestrictedTraceVanishingFieldUniverse
open ContinuumRestrictedClosedBoundaryUniverseAPI
open ContinuumRestrictedFirstVariationInterface
open ContinuumRestrictedKGResidualRoute
open ContinuumRestrictedSeparationPrinciple
open ContinuumSeparatingTestClassCandidate

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the residual-admissibility slice. -/
def phase1Blocker003A2A9ResidualAdmissibilityRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A9_RESIDUAL_ADMISSIBILITY_RETAINED"

/-- Outcome id for this bounded residual-admissibility surface. -/
def residualAdmissibilityOutcomeId : String :=
  "RESIDUAL_ADMISSIBILITY_CONDITION_RECORDED_" ++
    "ZERO_OPERATOR_ROUTE_DISCHARGED_NONZERO_RETAINED"

/-- Missing objects after the residual-admissibility surface. -/
inductive Phase1Blocker003A2A9MissingObject where
  | nonzeroOperatorResidualAdmissibility
  | nonzeroOperatorMapsRestrictedFields
  | nonzeroOperatorDomainClosure
  | boundaryTraceCompatibilityForResiduals
  | concreteSeparatingTestClass
  | nondegeneratePairingOrDensity
  | fullFieldContinuumRouteRecovery
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A9 objects. -/
def phase1Blocker003A2A9MissingObjectId :
    Phase1Blocker003A2A9MissingObject -> String
  | .nonzeroOperatorResidualAdmissibility =>
      "003A2A9_NONZERO_OPERATOR_RESIDUAL_ADMISSIBILITY_RETAINED"
  | .nonzeroOperatorMapsRestrictedFields =>
      "003A2A9_NONZERO_OPERATOR_MAPS_RESTRICTED_FIELDS_RETAINED"
  | .nonzeroOperatorDomainClosure =>
      "003A2A9_NONZERO_OPERATOR_DOMAIN_CLOSURE_RETAINED"
  | .boundaryTraceCompatibilityForResiduals =>
      "003A2A9_BOUNDARY_TRACE_COMPATIBILITY_FOR_RESIDUALS_RETAINED"
  | .concreteSeparatingTestClass =>
      "003A2A9_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"
  | .nondegeneratePairingOrDensity =>
      "003A2A9_NONDEGENERATE_PAIRING_OR_DENSITY_RETAINED"
  | .fullFieldContinuumRouteRecovery =>
      "003A2A9_FULL_FIELD_CONTINUUM_ROUTE_RECOVERY_RETAINED"

/-- The explicit remaining objects after this bounded surface. -/
def phase1Blocker003A2A9MissingObjectsV0 :
    List Phase1Blocker003A2A9MissingObject :=
  [ .nonzeroOperatorResidualAdmissibility
  , .nonzeroOperatorMapsRestrictedFields
  , .nonzeroOperatorDomainClosure
  , .boundaryTraceCompatibilityForResiduals
  , .concreteSeparatingTestClass
  , .nondegeneratePairingOrDensity
  , .fullFieldContinuumRouteRecovery
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a9_missing_objects_v0_expected :
    phase1Blocker003A2A9MissingObjectsV0 =
      [ .nonzeroOperatorResidualAdmissibility
      , .nonzeroOperatorMapsRestrictedFields
      , .nonzeroOperatorDomainClosure
      , .boundaryTraceCompatibilityForResiduals
      , .concreteSeparatingTestClass
      , .nondegeneratePairingOrDensity
      , .fullFieldContinuumRouteRecovery
      ] := by
  rfl

/-- KG residual admissibility for a restricted field class. -/
def KGResidualAdmittedFor {Point : Type}
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point) : Prop :=
  FieldClass phi -> FieldClass (Residual operator massSq phi)

/--
Uniform residual admissibility: every admitted field has an admitted KG
residual for the selected operator and mass.
-/
structure RestrictedKGResidualAdmissibility {Point : Type}
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop) where
  residual_admitted_of_admitted_field :
    forall phi : ContinuumField Point,
      KGResidualAdmittedFor operator massSq FieldClass phi

/--
Closure evidence sufficient to prove residual admissibility.  For a real
scalar kinetic operator, these are the domain-closure facts still missing.
-/
structure ResidualAdmissibilityClosureEvidence {Point : Type}
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop) where
  operator_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (operator phi)
  mass_term_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (fieldSMul massSq phi)
  add_closed :
    forall x y : ContinuumField Point,
      FieldClass x -> FieldClass y -> FieldClass (fieldAdd x y)

/-- Closure evidence supplies restricted KG residual admissibility. -/
def residualAdmissibilityOfClosureEvidence {Point : Type}
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (evidence :
      ResidualAdmissibilityClosureEvidence operator massSq FieldClass) :
    RestrictedKGResidualAdmissibility operator massSq FieldClass where
  residual_admitted_of_admitted_field := by
    intro phi hPhi
    exact evidence.add_closed (operator phi) (fieldSMul massSq phi)
      (evidence.operator_maps_admitted phi hPhi)
      (evidence.mass_term_maps_admitted phi hPhi)

/-- Residual admissibility discharges the admission premise in the A2A8 bridge. -/
theorem separating_test_class_candidate_upgrades_with_residual_admissibility
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (admissibility :
      RestrictedKGResidualAdmissibility operator massSq FieldClass)
    (hPhi : FieldClass phi)
    (hWeak :
      RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact separating_test_class_candidate_upgrades_weak_kg_residual
    integral operator massSq FieldClass phi candidate
    (admissibility.residual_admitted_of_admitted_field phi hPhi)
    hWeak

/--
Restricted stationarity, residual admissibility, and a supplied test-class
candidate give the old residual equation for an admitted base field.
-/
theorem restricted_stationarity_plus_candidate_and_residual_admissibility
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (admissibility :
      RestrictedKGResidualAdmissibility operator massSq FieldClass)
    (hPhi : FieldClass phi)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact separating_test_class_candidate_upgrades_with_residual_admissibility
    integral operator massSq FieldClass phi candidate admissibility hPhi
    (restricted_stationarity_implies_restricted_kg_residual_weak
      integral operator massSq FieldClass phi hStationary)

/-- A restricted KG conclusion upgrades under residual admissibility and a candidate. -/
theorem restricted_kg_conclusion_plus_candidate_and_admissibility
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (admissibility :
      RestrictedKGResidualAdmissibility operator massSq FieldClass)
    (conclusion :
      RestrictedKGResidualConclusion integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact separating_test_class_candidate_upgrades_with_residual_admissibility
    integral operator massSq FieldClass phi candidate admissibility
    conclusion.phi_admitted conclusion.residual_zero_on_admitted_tests

/-- The anchored trace-vanishing class is closed under scalar multiplication. -/
theorem anchored_trace_vanishing_field_smul {Point : Type}
    [Inhabited Point] (a : Real) (f : ContinuumField Point)
    (hf : AnchoredTraceVanishingFieldClass f) :
    AnchoredTraceVanishingFieldClass (fieldSMul a f) := by
  have hAnchor : f (default : Point) = 0 := by
    have hLeft := anchored_trace_vanishing_class_left_trace_zero f hf
    simpa [anchoredMeaningfulTwoSidedBoundaryTrace] using hLeft
  change
    (anchoredTraceZeroOperatorBoundaryProblem Point).trace.leftTrace
          (fieldSMul a f) = 0 ∧
      (anchoredTraceZeroOperatorBoundaryProblem Point).trace.rightTrace
          (fieldSMul a f) = 0
  constructor
  · simp [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace, fieldSMul, hAnchor]
  · simp [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace, fieldSMul, hAnchor]

/-- The anchored trace-vanishing class is closed under pointwise addition. -/
theorem anchored_trace_vanishing_field_add {Point : Type}
    [Inhabited Point] (x y : ContinuumField Point)
    (hx : AnchoredTraceVanishingFieldClass x)
    (hy : AnchoredTraceVanishingFieldClass y) :
    AnchoredTraceVanishingFieldClass (fieldAdd x y) := by
  have hxAnchor : x (default : Point) = 0 := by
    have hLeft := anchored_trace_vanishing_class_left_trace_zero x hx
    simpa [anchoredMeaningfulTwoSidedBoundaryTrace] using hLeft
  have hyAnchor : y (default : Point) = 0 := by
    have hLeft := anchored_trace_vanishing_class_left_trace_zero y hy
    simpa [anchoredMeaningfulTwoSidedBoundaryTrace] using hLeft
  change
    (anchoredTraceZeroOperatorBoundaryProblem Point).trace.leftTrace
          (fieldAdd x y) = 0 ∧
      (anchoredTraceZeroOperatorBoundaryProblem Point).trace.rightTrace
          (fieldAdd x y) = 0
  constructor
  · simp [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace, fieldAdd, hxAnchor, hyAnchor]
  · simp [anchoredTraceZeroOperatorBoundaryProblem,
      scalarKineticBoundaryProblemOfPair,
      anchoredTraceZeroOperatorClosedBoundaryPair,
      anchoredMeaningfulTwoSidedBoundaryTrace, fieldAdd, hxAnchor, hyAnchor]

/-- Closure evidence for the anchored zero-operator restricted route. -/
def anchoredZeroOperatorResidualClosureEvidence
    (Point : Type) [Inhabited Point] (massSq : Real) :
    ResidualAdmissibilityClosureEvidence
      (@zeroKineticOperator Point)
      massSq
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass where
  operator_maps_admitted := by
    intro _phi _hPhi
    change AnchoredTraceVanishingFieldClass (@zeroField Point)
    exact zero_field_in_anchored_trace_vanishing_class
  mass_term_maps_admitted := by
    intro phi hPhi
    change AnchoredTraceVanishingFieldClass (fieldSMul massSq phi)
    change AnchoredTraceVanishingFieldClass phi at hPhi
    exact anchored_trace_vanishing_field_smul massSq phi hPhi
  add_closed := by
    intro x y hx hy
    change AnchoredTraceVanishingFieldClass (fieldAdd x y)
    change AnchoredTraceVanishingFieldClass x at hx
    change AnchoredTraceVanishingFieldClass y at hy
    exact anchored_trace_vanishing_field_add x y hx hy

/-- The anchored zero-operator route has residual admissibility. -/
def anchoredZeroOperatorResidualAdmissibility
    (Point : Type) [Inhabited Point] (massSq : Real) :
    RestrictedKGResidualAdmissibility
      (@zeroKineticOperator Point)
      massSq
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass :=
  residualAdmissibilityOfClosureEvidence
    (@zeroKineticOperator Point)
    massSq
    (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass
    (anchoredZeroOperatorResidualClosureEvidence Point massSq)

/-- Status readout for this bounded residual-admissibility surface. -/
structure ResidualAdmissibilityAttemptStatus where
  residual_admissibility_condition_defined : Prop
  closure_evidence_surface_defined : Prop
  candidate_upgrade_bridge_recorded : Prop
  stationarity_upgrade_bridge_recorded : Prop
  anchored_zero_operator_residual_admissibility_discharged : Prop
  nonzero_operator_residual_admissibility_constructed : Prop
  nonzero_operator_residual_admissibility_not_constructed :
    Not nonzero_operator_residual_admissibility_constructed
  concrete_separating_test_class_constructed : Prop
  concrete_separating_test_class_not_constructed :
    Not concrete_separating_test_class_constructed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this bounded residual-admissibility surface. -/
def residualAdmissibilityAttemptStatusV0 :
    ResidualAdmissibilityAttemptStatus where
  residual_admissibility_condition_defined := True
  closure_evidence_surface_defined := True
  candidate_upgrade_bridge_recorded := True
  stationarity_upgrade_bridge_recorded := True
  anchored_zero_operator_residual_admissibility_discharged := True
  nonzero_operator_residual_admissibility_constructed := False
  nonzero_operator_residual_admissibility_not_constructed := by
    intro h
    exact h
  concrete_separating_test_class_constructed := False
  concrete_separating_test_class_not_constructed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id := phase1Blocker003A2A8SeparatingTestClassRetainedId
  retained_blocker_id := phase1Blocker003A2A9ResidualAdmissibilityRetainedId
  outcome_id := residualAdmissibilityOutcomeId

/-- Short local status alias. -/
def residualAdmissibilityStatusV0 :
    ResidualAdmissibilityAttemptStatus :=
  residualAdmissibilityAttemptStatusV0

/-- The residual-admissibility condition is defined. -/
theorem residual_admissibility_condition_defined_v0 :
    residualAdmissibilityStatusV0.residual_admissibility_condition_defined := by
  trivial

/-- The closure-evidence surface is defined. -/
theorem residual_admissibility_closure_evidence_defined_v0 :
    residualAdmissibilityStatusV0.closure_evidence_surface_defined := by
  trivial

/-- The A2A8 candidate upgrade bridge is recorded. -/
theorem residual_admissibility_candidate_bridge_recorded_v0 :
    residualAdmissibilityStatusV0.candidate_upgrade_bridge_recorded := by
  trivial

/-- The stationarity upgrade bridge is recorded. -/
theorem residual_admissibility_stationarity_bridge_recorded_v0 :
    residualAdmissibilityStatusV0.stationarity_upgrade_bridge_recorded := by
  trivial

/-- The anchored zero-operator residual-admissibility route is discharged. -/
theorem residual_admissibility_anchored_zero_operator_discharged_v0 :
    residualAdmissibilityStatusV0.anchored_zero_operator_residual_admissibility_discharged := by
  trivial

/-- No nonzero-operator residual-admissibility theorem is constructed. -/
theorem residual_admissibility_nonzero_operator_not_constructed_v0 :
    Not residualAdmissibilityStatusV0.nonzero_operator_residual_admissibility_constructed := by
  exact residualAdmissibilityStatusV0.nonzero_operator_residual_admissibility_not_constructed

/-- No concrete separating test class is constructed in this slice. -/
theorem residual_admissibility_test_class_not_constructed_v0 :
    Not residualAdmissibilityStatusV0.concrete_separating_test_class_constructed := by
  exact residualAdmissibilityStatusV0.concrete_separating_test_class_not_constructed

/-- The attempt exposes the parent retained blocker id. -/
theorem residual_admissibility_parent_retained_id_v0 :
    residualAdmissibilityStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A8SeparatingTestClassRetainedId := by
  simp [residualAdmissibilityStatusV0, residualAdmissibilityAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem residual_admissibility_retained_id_v0 :
    residualAdmissibilityStatusV0.retained_blocker_id =
      phase1Blocker003A2A9ResidualAdmissibilityRetainedId := by
  simp [residualAdmissibilityStatusV0, residualAdmissibilityAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem residual_admissibility_outcome_id_v0 :
    residualAdmissibilityStatusV0.outcome_id =
      residualAdmissibilityOutcomeId := by
  simp [residualAdmissibilityStatusV0, residualAdmissibilityAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded surface. -/
theorem residual_admissibility_phase2_not_authorized_v0 :
    Not residualAdmissibilityStatusV0.phase2Authorized := by
  exact residualAdmissibilityStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained residual-admissibility route. -/
def phase1Blocker003A2A9ResidualAdmissibilityV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a9_residual_admissibility_v0_phase2_not_authorized :
    Not phase1Blocker003A2A9ResidualAdmissibilityV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumResidualAdmissibility
end QFT
end ToeFormal
