/-
ToeFormal/QFT/ContinuumNonzeroScalarKineticOperatorDomainClosure.lean

Nonzero scalar kinetic operator-domain closure surface for
PHASE1-BLOCKER-003A2A10.

Scope:
- name the domain/trace closure package needed for a nonzero scalar kinetic
  operator over a restricted field class
- state that the operator maps admitted fields into the restricted class
- state mass-term and addition closure, hence residual admissibility
- state trace-vanishing compatibility for operator images and residuals
- prove that supplied closure evidence feeds A2A9
- keep concrete nonzero operator construction, Green identity, separating
  test-class construction, full-field route recovery, and Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumResidualAdmissibility

namespace ToeFormal
namespace QFT
namespace ContinuumNonzeroScalarKineticOperatorDomainClosure

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumResidualAdmissibility
open ContinuumRestrictedKGResidualRoute
open ContinuumSeparatingTestClassCandidate

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the nonzero operator-domain closure surface. -/
def phase1Blocker003A2A10NonzeroOperatorDomainClosureRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A10_NONZERO_SCALAR_KINETIC_OPERATOR_" ++
    "DOMAIN_CLOSURE_RETAINED"

/-- Outcome id for this bounded domain-closure surface. -/
def nonzeroOperatorDomainClosureOutcomeId : String :=
  "NONZERO_OPERATOR_DOMAIN_CLOSURE_CONDITION_RECORDED_" ++
    "CONCRETE_PROOF_RETAINED"

/-- Missing objects after the nonzero operator-domain closure surface. -/
inductive Phase1Blocker003A2A10MissingObject where
  | concreteNonzeroScalarKineticOperator
  | concreteRestrictedFunctionSpace
  | nonzeroOperatorMapsRestrictedFields
  | nonzeroOperatorTraceCompatibility
  | nonzeroOperatorGreenIdentity
  | concreteSeparatingTestClass
  | fullFieldContinuumRouteRecovery
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A10 objects. -/
def phase1Blocker003A2A10MissingObjectId :
    Phase1Blocker003A2A10MissingObject -> String
  | .concreteNonzeroScalarKineticOperator =>
      "003A2A10_CONCRETE_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .concreteRestrictedFunctionSpace =>
      "003A2A10_CONCRETE_RESTRICTED_FUNCTION_SPACE_RETAINED"
  | .nonzeroOperatorMapsRestrictedFields =>
      "003A2A10_NONZERO_OPERATOR_MAPS_RESTRICTED_FIELDS_RETAINED"
  | .nonzeroOperatorTraceCompatibility =>
      "003A2A10_NONZERO_OPERATOR_TRACE_COMPATIBILITY_RETAINED"
  | .nonzeroOperatorGreenIdentity =>
      "003A2A10_NONZERO_OPERATOR_GREEN_IDENTITY_RETAINED"
  | .concreteSeparatingTestClass =>
      "003A2A10_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"
  | .fullFieldContinuumRouteRecovery =>
      "003A2A10_FULL_FIELD_CONTINUUM_ROUTE_RECOVERY_RETAINED"

/-- The explicit remaining objects after this bounded surface. -/
def phase1Blocker003A2A10MissingObjectsV0 :
    List Phase1Blocker003A2A10MissingObject :=
  [ .concreteNonzeroScalarKineticOperator
  , .concreteRestrictedFunctionSpace
  , .nonzeroOperatorMapsRestrictedFields
  , .nonzeroOperatorTraceCompatibility
  , .nonzeroOperatorGreenIdentity
  , .concreteSeparatingTestClass
  , .fullFieldContinuumRouteRecovery
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a10_missing_objects_v0_expected :
    phase1Blocker003A2A10MissingObjectsV0 =
      [ .concreteNonzeroScalarKineticOperator
      , .concreteRestrictedFunctionSpace
      , .nonzeroOperatorMapsRestrictedFields
      , .nonzeroOperatorTraceCompatibility
      , .nonzeroOperatorGreenIdentity
      , .concreteSeparatingTestClass
      , .fullFieldContinuumRouteRecovery
      ] := by
  rfl

/-- A scalar kinetic operator is nonzero when it is nonzero on some field. -/
def ScalarKineticOperatorNonzero {Point : Type}
    (operator : ContinuumField Point -> ContinuumField Point) : Prop :=
  Exists fun phi : ContinuumField Point => operator phi ≠ 0

/--
Domain and trace closure package for a nonzero scalar kinetic operator over a
restricted field class.
-/
structure NonzeroScalarKineticOperatorDomainClosure {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop) where
  operator_nonzero : ScalarKineticOperatorNonzero problem.kineticOperator
  admitted_fields_in_operator_domain :
    forall phi : ContinuumField Point,
      FieldClass phi -> problem.InOperatorDomain phi
  admitted_fields_trace_vanishing :
    forall phi : ContinuumField Point,
      FieldClass phi -> TraceVanishingCompactSupportOrDecay problem phi
  operator_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (problem.kineticOperator phi)
  mass_term_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (fieldSMul massSq phi)
  add_closed :
    forall x y : ContinuumField Point,
      FieldClass x -> FieldClass y -> FieldClass (fieldAdd x y)

/-- Supplied nonzero domain closure yields A2A9 closure evidence. -/
def residualClosureEvidenceOfNonzeroOperatorDomainClosure {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass) :
    ResidualAdmissibilityClosureEvidence
      problem.kineticOperator massSq FieldClass where
  operator_maps_admitted := closure.operator_maps_admitted
  mass_term_maps_admitted := closure.mass_term_maps_admitted
  add_closed := closure.add_closed

/-- Supplied nonzero domain closure gives residual admissibility. -/
def residualAdmissibilityOfNonzeroOperatorDomainClosure {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass) :
    RestrictedKGResidualAdmissibility
      problem.kineticOperator massSq FieldClass :=
  residualAdmissibilityOfClosureEvidence
    problem.kineticOperator massSq FieldClass
    (residualClosureEvidenceOfNonzeroOperatorDomainClosure
      problem massSq FieldClass closure)

/-- Supplied closure proves the operator image has zero boundary trace. -/
theorem operator_image_trace_vanishing_of_nonzero_domain_closure
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass)
    (phi : ContinuumField Point)
    (hPhi : FieldClass phi) :
    TraceVanishingCompactSupportOrDecay problem (problem.kineticOperator phi) := by
  exact closure.admitted_fields_trace_vanishing
    (problem.kineticOperator phi)
    (closure.operator_maps_admitted phi hPhi)

/-- Supplied closure proves the KG residual is admitted. -/
theorem residual_admitted_of_nonzero_domain_closure
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass)
    (phi : ContinuumField Point)
    (hPhi : FieldClass phi) :
    FieldClass (Residual problem.kineticOperator massSq phi) := by
  let admissibility :=
    residualAdmissibilityOfNonzeroOperatorDomainClosure
      problem massSq FieldClass closure
  exact admissibility.residual_admitted_of_admitted_field phi hPhi

/-- Supplied closure proves the KG residual has zero boundary trace. -/
theorem residual_trace_vanishing_of_nonzero_domain_closure
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass)
    (phi : ContinuumField Point)
    (hPhi : FieldClass phi) :
    TraceVanishingCompactSupportOrDecay
      problem (Residual problem.kineticOperator massSq phi) := by
  exact closure.admitted_fields_trace_vanishing
    (Residual problem.kineticOperator massSq phi)
    (residual_admitted_of_nonzero_domain_closure
      problem massSq FieldClass closure phi hPhi)

/--
With a separating test-class candidate, supplied nonzero domain closure upgrades
restricted stationarity to the residual equation for admitted base fields.
-/
theorem restricted_stationarity_plus_candidate_and_nonzero_domain_closure
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (phi : ContinuumField Point)
    (candidate : SeparatingTestClassCandidate problem.integral FieldClass)
    (closure :
      NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass)
    (hPhi : FieldClass phi)
    (hStationary :
      RestrictedFirstVariationStationaryFor
        problem.integral problem.kineticOperator massSq FieldClass phi) :
    ResidualEquation (Residual problem.kineticOperator massSq phi) := by
  exact restricted_stationarity_plus_candidate_and_residual_admissibility
    problem.integral problem.kineticOperator massSq FieldClass phi
    candidate
    (residualAdmissibilityOfNonzeroOperatorDomainClosure
      problem massSq FieldClass closure)
    hPhi hStationary

/-- Status readout for this bounded nonzero operator-domain closure surface. -/
structure NonzeroOperatorDomainClosureAttemptStatus where
  closure_surface_defined : Prop
  residual_closure_evidence_bridge_recorded : Prop
  residual_admissibility_bridge_recorded : Prop
  operator_trace_compatibility_recorded : Prop
  residual_trace_compatibility_recorded : Prop
  candidate_stationarity_upgrade_recorded : Prop
  concrete_nonzero_operator_closure_constructed : Prop
  concrete_nonzero_operator_closure_not_constructed :
    Not concrete_nonzero_operator_closure_constructed
  green_identity_for_nonzero_operator_closed : Prop
  green_identity_for_nonzero_operator_not_closed :
    Not green_identity_for_nonzero_operator_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this bounded domain-closure surface. -/
def nonzeroOperatorDomainClosureAttemptStatusV0 :
    NonzeroOperatorDomainClosureAttemptStatus where
  closure_surface_defined := True
  residual_closure_evidence_bridge_recorded := True
  residual_admissibility_bridge_recorded := True
  operator_trace_compatibility_recorded := True
  residual_trace_compatibility_recorded := True
  candidate_stationarity_upgrade_recorded := True
  concrete_nonzero_operator_closure_constructed := False
  concrete_nonzero_operator_closure_not_constructed := by
    intro h
    exact h
  green_identity_for_nonzero_operator_closed := False
  green_identity_for_nonzero_operator_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id := phase1Blocker003A2A9ResidualAdmissibilityRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A10NonzeroOperatorDomainClosureRetainedId
  outcome_id := nonzeroOperatorDomainClosureOutcomeId

/-- Short local status alias. -/
def nonzeroOperatorDomainClosureStatusV0 :
    NonzeroOperatorDomainClosureAttemptStatus :=
  nonzeroOperatorDomainClosureAttemptStatusV0

/-- The nonzero operator-domain closure surface is defined. -/
theorem nonzero_operator_domain_closure_surface_defined_v0 :
    nonzeroOperatorDomainClosureStatusV0.closure_surface_defined := by
  trivial

/-- The bridge to A2A9 closure evidence is recorded. -/
theorem nonzero_operator_residual_closure_bridge_recorded_v0 :
    nonzeroOperatorDomainClosureStatusV0.residual_closure_evidence_bridge_recorded := by
  trivial

/-- The bridge to residual admissibility is recorded. -/
theorem nonzero_operator_residual_admissibility_bridge_recorded_v0 :
    nonzeroOperatorDomainClosureStatusV0.residual_admissibility_bridge_recorded := by
  trivial

/-- Operator trace compatibility is recorded conditionally. -/
theorem nonzero_operator_trace_compatibility_recorded_v0 :
    nonzeroOperatorDomainClosureStatusV0.operator_trace_compatibility_recorded := by
  trivial

/-- Residual trace compatibility is recorded conditionally. -/
theorem nonzero_operator_residual_trace_compatibility_recorded_v0 :
    nonzeroOperatorDomainClosureStatusV0.residual_trace_compatibility_recorded := by
  trivial

/-- Candidate stationarity upgrade is recorded conditionally. -/
theorem nonzero_operator_candidate_stationarity_upgrade_recorded_v0 :
    nonzeroOperatorDomainClosureStatusV0.candidate_stationarity_upgrade_recorded := by
  trivial

/-- No concrete nonzero-operator closure theorem is constructed in this slice. -/
theorem nonzero_operator_domain_closure_concrete_not_constructed_v0 :
    Not nonzeroOperatorDomainClosureStatusV0.concrete_nonzero_operator_closure_constructed := by
  exact nonzeroOperatorDomainClosureStatusV0.concrete_nonzero_operator_closure_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem nonzero_operator_domain_closure_green_identity_not_closed_v0 :
    Not nonzeroOperatorDomainClosureStatusV0.green_identity_for_nonzero_operator_closed := by
  exact nonzeroOperatorDomainClosureStatusV0.green_identity_for_nonzero_operator_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem nonzero_operator_domain_closure_parent_retained_id_v0 :
    nonzeroOperatorDomainClosureStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A9ResidualAdmissibilityRetainedId := by
  simp [nonzeroOperatorDomainClosureStatusV0,
    nonzeroOperatorDomainClosureAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem nonzero_operator_domain_closure_retained_id_v0 :
    nonzeroOperatorDomainClosureStatusV0.retained_blocker_id =
      phase1Blocker003A2A10NonzeroOperatorDomainClosureRetainedId := by
  simp [nonzeroOperatorDomainClosureStatusV0,
    nonzeroOperatorDomainClosureAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem nonzero_operator_domain_closure_outcome_id_v0 :
    nonzeroOperatorDomainClosureStatusV0.outcome_id =
      nonzeroOperatorDomainClosureOutcomeId := by
  simp [nonzeroOperatorDomainClosureStatusV0,
    nonzeroOperatorDomainClosureAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded surface. -/
theorem nonzero_operator_domain_closure_phase2_not_authorized_v0 :
    Not nonzeroOperatorDomainClosureStatusV0.phase2Authorized := by
  exact nonzeroOperatorDomainClosureStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained domain-closure route. -/
def phase1Blocker003A2A10NonzeroOperatorDomainClosureV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a10_domain_closure_v0_phase2_not_authorized :
    Not phase1Blocker003A2A10NonzeroOperatorDomainClosureV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumNonzeroScalarKineticOperatorDomainClosure
end QFT
end ToeFormal
