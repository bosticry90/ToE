/-
ToeFormal/QFT/ContinuumSeparatingTestClassCandidate.lean

Separating test-class candidate surface for
PHASE1-BLOCKER-003A2A8.

Scope:
- name the stronger admitted test class needed after the A2A7 obstruction
- state the separation property for admitted residuals
- prove that supplied test-class evidence feeds the A2A7 admitted restricted
  separation route
- prove the weak restricted KG upgrade through that supplied evidence
- keep concrete test-class construction, nondegenerate continuum pairing,
  nonzero kinetic analysis, operator-domain closure, full-field route recovery,
  and Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumRestrictedSeparationPrinciple

namespace ToeFormal
namespace QFT
namespace ContinuumSeparatingTestClassCandidate

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumRestrictedFirstVariationInterface
open ContinuumRestrictedKGResidualRoute
open ContinuumRestrictedSeparationPrinciple

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the separating test-class candidate slice. -/
def phase1Blocker003A2A8SeparatingTestClassRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A8_SEPARATING_TEST_CLASS_RETAINED"

/-- Outcome id for this bounded candidate surface. -/
def separatingTestClassCandidateOutcomeId : String :=
  "SEPARATING_TEST_CLASS_CANDIDATE_SURFACE_RECORDED_" ++
    "CONSTRUCTION_RETAINED"

/-- Missing objects after the separating test-class candidate surface. -/
inductive Phase1Blocker003A2A8MissingObject where
  | concreteSeparatingTestClass
  | testClassAdmissionIntoRestrictedVariations
  | residualAdmissibilityForKGResidual
  | nondegeneratePairingOnTestClass
  | densityOrDualitySeparationTheorem
  | nonzeroScalarKineticOperator
  | operatorDomainClosureForNonzeroOperator
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A8 objects. -/
def phase1Blocker003A2A8MissingObjectId :
    Phase1Blocker003A2A8MissingObject -> String
  | .concreteSeparatingTestClass =>
      "003A2A8_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"
  | .testClassAdmissionIntoRestrictedVariations =>
      "003A2A8_TEST_CLASS_ADMISSION_INTO_RESTRICTED_VARIATIONS_RETAINED"
  | .residualAdmissibilityForKGResidual =>
      "003A2A8_RESIDUAL_ADMISSIBILITY_FOR_KG_RESIDUAL_RETAINED"
  | .nondegeneratePairingOnTestClass =>
      "003A2A8_NONDEGENERATE_PAIRING_ON_TEST_CLASS_RETAINED"
  | .densityOrDualitySeparationTheorem =>
      "003A2A8_DENSITY_OR_DUALITY_SEPARATION_THEOREM_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A8_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A8_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"

/-- The explicit remaining objects after this bounded candidate surface. -/
def phase1Blocker003A2A8MissingObjectsV0 :
    List Phase1Blocker003A2A8MissingObject :=
  [ .concreteSeparatingTestClass
  , .testClassAdmissionIntoRestrictedVariations
  , .residualAdmissibilityForKGResidual
  , .nondegeneratePairingOnTestClass
  , .densityOrDualitySeparationTheorem
  , .nonzeroScalarKineticOperator
  , .operatorDomainClosureForNonzeroOperator
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a8_missing_objects_v0_expected :
    phase1Blocker003A2A8MissingObjectsV0 =
      [ .concreteSeparatingTestClass
      , .testClassAdmissionIntoRestrictedVariations
      , .residualAdmissibilityForKGResidual
      , .nondegeneratePairingOnTestClass
      , .densityOrDualitySeparationTheorem
      , .nonzeroScalarKineticOperator
      , .operatorDomainClosureForNonzeroOperator
      ] := by
  rfl

/-- Pairing vanishing against a selected test class. -/
def TestClassPairingsVanish {Point : Type}
    (integral : ContinuumField Point -> Real)
    (TestClass : ContinuumField Point -> Prop)
    (residual : ContinuumField Point) : Prop :=
  forall eta : ContinuumField Point,
    TestClass eta -> ContinuumPair integral eta residual = 0

/--
Candidate package for a stronger test class.  It does not construct a class;
it records exactly what a supplied class must provide to separate admitted
residuals and feed the A2A7 admitted separation route.
-/
structure SeparatingTestClassCandidate {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop) where
  TestClass : ContinuumField Point -> Prop
  test_class_admitted :
    forall eta : ContinuumField Point, TestClass eta -> FieldClass eta
  residual_zero_of_test_pairings_zero :
    forall residual : ContinuumField Point,
      FieldClass residual ->
      TestClassPairingsVanish integral TestClass residual ->
        ResidualEquation residual

/-- Restricted stationarity supplies vanishing against the candidate test class. -/
theorem test_class_pairings_vanish_of_restricted_stationary
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (residual : ContinuumField Point)
    (hWeak : RestrictedStationaryFor integral FieldClass residual) :
    TestClassPairingsVanish integral candidate.TestClass residual := by
  intro eta hEta
  exact hWeak eta (candidate.test_class_admitted eta hEta)

/-- A supplied separating test-class candidate gives admitted restricted separation. -/
def admittedRestrictedSeparationOfSeparatingTestClassCandidate
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate : SeparatingTestClassCandidate integral FieldClass) :
    AdmittedRestrictedSeparationPrinciple integral FieldClass where
  residual_zero_of_admitted_restricted_pairings_zero := by
    intro residual hResidual hWeak
    exact candidate.residual_zero_of_test_pairings_zero residual hResidual
      (test_class_pairings_vanish_of_restricted_stationary
        integral FieldClass candidate residual hWeak)

/-- A supplied candidate upgrades weak KG residual vanishing when the residual is admitted. -/
theorem separating_test_class_candidate_upgrades_weak_kg_residual
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (hResidual : FieldClass (Residual operator massSq phi))
    (hWeak :
      RestrictedKGResidualWeakEquation integral operator massSq FieldClass phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact admitted_restricted_separation_upgrades_weak_kg_residual
    integral operator massSq FieldClass phi
    (admittedRestrictedSeparationOfSeparatingTestClassCandidate
      integral FieldClass candidate)
    hResidual hWeak

/-- Restricted stationarity plus a supplied candidate gives restricted residual zero. -/
theorem restricted_stationarity_plus_separating_test_class_candidate
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        integral operator massSq FieldClass phi) :
    RestrictedResidualEquation FieldClass (Residual operator massSq phi) := by
  exact restricted_stationarity_plus_admitted_separation_gives_restricted_residual
    integral operator massSq FieldClass phi
    (admittedRestrictedSeparationOfSeparatingTestClassCandidate
      integral FieldClass candidate)
    hStationary

/--
If every residual is admitted by the restricted class, a candidate test class
also recovers the stronger restricted separation principle.  The hypothesis is
explicit because this slice does not prove residual admissibility.
-/
def restrictedSeparationOfSeparatingTestClassCandidateWithAllResiduals
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate : SeparatingTestClassCandidate integral FieldClass)
    (allResidualsAdmitted :
      forall residual : ContinuumField Point, FieldClass residual) :
    RestrictedSeparationPrinciple integral FieldClass where
  residual_zero_of_all_restricted_pairings_zero := by
    intro residual hWeak
    exact candidate.residual_zero_of_test_pairings_zero residual
      (allResidualsAdmitted residual)
      (test_class_pairings_vanish_of_restricted_stationary
        integral FieldClass candidate residual hWeak)

/-- Status readout for this bounded separating test-class candidate surface. -/
structure SeparatingTestClassCandidateAttemptStatus where
  candidate_surface_defined : Prop
  test_pairing_vanishing_defined : Prop
  admitted_separation_bridge_recorded : Prop
  weak_kg_upgrade_bridge_recorded : Prop
  strong_bridge_requires_residual_admissibility : Prop
  concrete_test_class_constructed : Prop
  concrete_test_class_not_constructed : Not concrete_test_class_constructed
  nondegenerate_pairing_constructed : Prop
  nondegenerate_pairing_not_constructed : Not nondegenerate_pairing_constructed
  nonzero_operator_green_identity_closed : Prop
  nonzero_operator_green_identity_not_closed :
    Not nonzero_operator_green_identity_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this candidate surface. -/
def separatingTestClassCandidateAttemptStatusV0 :
    SeparatingTestClassCandidateAttemptStatus where
  candidate_surface_defined := True
  test_pairing_vanishing_defined := True
  admitted_separation_bridge_recorded := True
  weak_kg_upgrade_bridge_recorded := True
  strong_bridge_requires_residual_admissibility := True
  concrete_test_class_constructed := False
  concrete_test_class_not_constructed := by
    intro h
    exact h
  nondegenerate_pairing_constructed := False
  nondegenerate_pairing_not_constructed := by
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
    phase1Blocker003A2A7RestrictedSeparationPrincipleRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A8SeparatingTestClassRetainedId
  outcome_id := separatingTestClassCandidateOutcomeId

/-- Short local status alias. -/
def separatingTestClassStatusV0 :
    SeparatingTestClassCandidateAttemptStatus :=
  separatingTestClassCandidateAttemptStatusV0

/-- The separating test-class candidate surface is defined. -/
theorem separating_test_class_candidate_surface_defined_v0 :
    separatingTestClassStatusV0.candidate_surface_defined := by
  trivial

/-- Pairing vanishing against the candidate test class is defined. -/
theorem separating_test_class_pairing_vanishing_defined_v0 :
    separatingTestClassStatusV0.test_pairing_vanishing_defined := by
  trivial

/-- The admitted restricted-separation bridge is recorded. -/
theorem separating_test_class_admitted_bridge_recorded_v0 :
    separatingTestClassStatusV0.admitted_separation_bridge_recorded := by
  trivial

/-- The weak KG upgrade bridge is recorded. -/
theorem separating_test_class_weak_kg_bridge_recorded_v0 :
    separatingTestClassStatusV0.weak_kg_upgrade_bridge_recorded := by
  trivial

/-- The stronger bridge still requires residual admissibility. -/
theorem separating_test_class_strong_bridge_requires_residuals_v0 :
    separatingTestClassStatusV0.strong_bridge_requires_residual_admissibility := by
  trivial

/-- No concrete separating test class is constructed in this slice. -/
theorem separating_test_class_concrete_not_constructed_v0 :
    Not separatingTestClassStatusV0.concrete_test_class_constructed := by
  exact separatingTestClassStatusV0.concrete_test_class_not_constructed

/-- No nondegenerate continuum pairing is constructed in this slice. -/
theorem separating_test_class_nondegenerate_pairing_not_constructed_v0 :
    Not separatingTestClassStatusV0.nondegenerate_pairing_constructed := by
  exact separatingTestClassStatusV0.nondegenerate_pairing_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem separating_test_class_nonzero_operator_green_not_closed_v0 :
    Not separatingTestClassStatusV0.nonzero_operator_green_identity_closed := by
  exact separatingTestClassStatusV0.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem separating_test_class_parent_retained_id_v0 :
    separatingTestClassStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A7RestrictedSeparationPrincipleRetainedId := by
  simp [separatingTestClassStatusV0,
    separatingTestClassCandidateAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem separating_test_class_retained_id_v0 :
    separatingTestClassStatusV0.retained_blocker_id =
      phase1Blocker003A2A8SeparatingTestClassRetainedId := by
  simp [separatingTestClassStatusV0,
    separatingTestClassCandidateAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem separating_test_class_outcome_id_v0 :
    separatingTestClassStatusV0.outcome_id =
      separatingTestClassCandidateOutcomeId := by
  simp [separatingTestClassStatusV0,
    separatingTestClassCandidateAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded candidate surface. -/
theorem separating_test_class_phase2_not_authorized_v0 :
    Not separatingTestClassStatusV0.phase2Authorized := by
  exact separatingTestClassStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained test-class route. -/
def phase1Blocker003A2A8SeparatingTestClassV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a8_separating_test_class_v0_phase2_not_authorized :
    Not phase1Blocker003A2A8SeparatingTestClassV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumSeparatingTestClassCandidate
end QFT
end ToeFormal
