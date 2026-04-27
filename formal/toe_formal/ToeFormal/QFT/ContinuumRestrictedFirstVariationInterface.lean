/-
ToeFormal/QFT/ContinuumRestrictedFirstVariationInterface.lean

Restricted first-variation interface for
PHASE1-BLOCKER-003A2A5.

Scope:
- define a first-variation boundary interface over a restricted field class
- prove the algebraic action-shift route using restricted integration by parts
  for admitted base/variation pairs
- define the adapter condition needed to recover the existing full-field
  `ContinuumFirstVariationObligations`
- prove the anchored meaningful-trace restricted route cannot supply that
  full-field adapter, because the restricted class is not all fields
- keep nonzero kinetic analysis, full first-variation closure,
  operator-domain closure, residual separation, and Phase 2 out of scope
-/

import ToeFormal.QFT.ContinuumRestrictedClosedBoundaryUniverseAPI

namespace ToeFormal
namespace QFT
namespace ContinuumRestrictedFirstVariationInterface

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumRestrictedTraceVanishingFieldUniverse
open ContinuumRestrictedClosedBoundaryUniverseAPI

set_option autoImplicit false

noncomputable section

/-- Retained blocker after defining the restricted first-variation interface. -/
def phase1Blocker003A2A5RestrictedFirstVariationInterfaceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A5_RESTRICTED_FIRST_VARIATION_INTERFACE_RETAINED"

/-- Outcome id for this bounded interface slice. -/
def restrictedFirstVariationInterfaceOutcomeId : String :=
  "RESTRICTED_FIRST_VARIATION_INTERFACE_DEFINED_ADAPTER_RETAINED"

/-- Missing objects after the restricted first-variation interface slice. -/
inductive Phase1Blocker003A2A5MissingObject where
  | restrictedToFullFirstVariationAdapter
  | allFieldsInRestrictedClass
  | restrictedSeparationPrinciple
  | nonzeroScalarKineticOperator
  | greenIdentityForNonzeroOperator
  | operatorDomainClosureForNonzeroOperator
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A5 objects. -/
def phase1Blocker003A2A5MissingObjectId :
    Phase1Blocker003A2A5MissingObject -> String
  | .restrictedToFullFirstVariationAdapter =>
      "003A2A5_RESTRICTED_TO_FULL_FIRST_VARIATION_ADAPTER_RETAINED"
  | .allFieldsInRestrictedClass =>
      "003A2A5_ALL_FIELDS_IN_RESTRICTED_CLASS_RETAINED"
  | .restrictedSeparationPrinciple =>
      "003A2A5_RESTRICTED_SEPARATION_PRINCIPLE_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A5_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .greenIdentityForNonzeroOperator =>
      "003A2A5_GREEN_IDENTITY_FOR_NONZERO_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A5_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"

/-- The explicit remaining objects after this bounded attempt. -/
def phase1Blocker003A2A5MissingObjectsV0 :
    List Phase1Blocker003A2A5MissingObject :=
  [ .restrictedToFullFirstVariationAdapter
  , .allFieldsInRestrictedClass
  , .restrictedSeparationPrinciple
  , .nonzeroScalarKineticOperator
  , .greenIdentityForNonzeroOperator
  , .operatorDomainClosureForNonzeroOperator
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a5_missing_objects_v0_expected :
    phase1Blocker003A2A5MissingObjectsV0 =
      [ .restrictedToFullFirstVariationAdapter
      , .allFieldsInRestrictedClass
      , .restrictedSeparationPrinciple
      , .nonzeroScalarKineticOperator
      , .greenIdentityForNonzeroOperator
      , .operatorDomainClosureForNonzeroOperator
      ] := by
  rfl

/-- Stationarity tested only against variations in a restricted field class. -/
def RestrictedStationaryFor {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (residual : ContinuumField Point) : Prop :=
  forall eta : ContinuumField Point,
    FieldClass eta -> ContinuumPair integral eta residual = 0

/-- Separation principle for a restricted test-field class. -/
structure RestrictedSeparationPrinciple {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop) where
  residual_zero_of_all_restricted_pairings_zero :
    forall residual : ContinuumField Point,
      RestrictedStationaryFor integral FieldClass residual -> residual = 0

/-- Boundary portion of the first-variation interface over a field class. -/
structure RestrictedFirstVariationBoundaryInterface {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point) where
  restricted_boundary_model : RestrictedBoundaryTermModel integral operator

/-- Restricted first-variation obligations. -/
structure RestrictedFirstVariationObligations {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point) where
  integral_linear : LinearIntegral integral
  operator_linear : LinearOperator operator
  restricted_boundary_model : RestrictedBoundaryTermModel integral operator
  restricted_separation :
    RestrictedSeparationPrinciple integral restricted_boundary_model.FieldClass

/-- Witness that a selected base/variation pair is admitted by the interface. -/
structure RestrictedFirstVariationPairWitness {Point : Type}
    {integral : ContinuumField Point -> Real}
    {operator : ContinuumField Point -> ContinuumField Point}
    (interface : RestrictedFirstVariationBoundaryInterface integral operator)
    (phi eta : ContinuumField Point) where
  phi_in_class : interface.restricted_boundary_model.FieldClass phi
  eta_in_class : interface.restricted_boundary_model.FieldClass eta

/-- Restricted integration by parts for an admitted pair. -/
theorem restricted_first_variation_ibp_for_admitted_pair {Point : Type}
    {integral : ContinuumField Point -> Real}
    {operator : ContinuumField Point -> ContinuumField Point}
    (interface : RestrictedFirstVariationBoundaryInterface integral operator)
    (x y : ContinuumField Point)
    (hx : interface.restricted_boundary_model.FieldClass x)
    (hy : interface.restricted_boundary_model.FieldClass y) :
    ContinuumPair integral x (operator y) =
      ContinuumPair integral y (operator x) := by
  exact restricted_boundary_term_model_suffices_for_restricted_ibp
    integral operator interface.restricted_boundary_model x y hx hy

/-- Exact kinetic expansion using restricted integration by parts. -/
theorem restricted_kinetic_pair_shift_expansion {Point : Type}
    (integral : ContinuumField Point -> Real)
    (hIntegral : LinearIntegral integral)
    (operator : ContinuumField Point -> ContinuumField Point)
    (hLinear : LinearOperator operator)
    (hBoundary : RestrictedBoundaryTermModel integral operator)
    (eps : Real)
    (phi eta : ContinuumField Point)
    (hphi : hBoundary.FieldClass phi)
    (heta : hBoundary.FieldClass eta) :
    ContinuumPair integral (fieldAdd phi (fieldSMul eps eta))
        (operator (fieldAdd phi (fieldSMul eps eta))) =
      ContinuumPair integral phi (operator phi) +
        2 * eps * ContinuumPair integral eta (operator phi) +
        eps ^ 2 * ContinuumPair integral eta (operator eta) := by
  rw [hLinear.map_add, hLinear.map_smul]
  rw [pair_add_left integral hIntegral, pair_add_right integral hIntegral]
  rw [pair_smul_right integral hIntegral, pair_smul_left integral hIntegral]
  rw [pair_add_right integral hIntegral, pair_smul_right integral hIntegral]
  rw [restricted_boundary_term_model_suffices_for_restricted_ibp
    integral operator hBoundary phi eta hphi heta]
  ring

/--
Restricted first-variation action-shift expansion.  This mirrors the existing
global algebraic theorem, but the boundary step is required only for the
admitted base field and variation.
-/
theorem restricted_action_shift_expansion {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (obligation : RestrictedFirstVariationObligations integral operator)
    (massSq eps : Real)
    (phi eta : ContinuumField Point)
    (hphi : obligation.restricted_boundary_model.FieldClass phi)
    (heta : obligation.restricted_boundary_model.FieldClass eta) :
    ContinuumFirstVariation.Action integral operator massSq
        (VariationFamily phi eta eps) =
      ContinuumFirstVariation.Action integral operator massSq phi +
        eps * FirstVariation integral operator massSq phi eta +
        eps ^ 2 *
          ContinuumFirstVariation.Action integral operator massSq eta := by
  unfold ContinuumFirstVariation.Action VariationFamily
  rw [restricted_kinetic_pair_shift_expansion
    integral obligation.integral_linear
    operator obligation.operator_linear obligation.restricted_boundary_model
    eps phi eta hphi heta]
  rw [mass_pair_shift_expansion integral obligation.integral_linear eps phi eta]
  rw [residual_pair_eq integral obligation.integral_linear operator massSq phi eta]
  ring

/-- Restricted algebraic derivative-at-zero statement. -/
theorem restricted_action_has_algebraic_derivative_at_zero {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (obligation : RestrictedFirstVariationObligations integral operator)
    (massSq : Real)
    (phi eta : ContinuumField Point)
    (hphi : obligation.restricted_boundary_model.FieldClass phi)
    (heta : obligation.restricted_boundary_model.FieldClass eta) :
    HasAlgebraicDerivativeAtZero
      (fun eps =>
        ContinuumFirstVariation.Action integral operator massSq
          (VariationFamily phi eta eps))
      (ContinuumFirstVariation.Action integral operator massSq phi)
      (FirstVariation integral operator massSq phi eta) := by
  refine ⟨ContinuumFirstVariation.Action integral operator massSq eta, ?_⟩
  intro eps
  exact restricted_action_shift_expansion
    integral operator obligation massSq eps phi eta hphi heta

/-- Restricted stationarity plus restricted separation implies residual zero. -/
theorem restricted_stationary_implies_residual_zero {Point : Type}
    (integral : ContinuumField Point -> Real)
    (FieldClass : ContinuumField Point -> Prop)
    (separation : RestrictedSeparationPrinciple integral FieldClass)
    (residual : ContinuumField Point)
    (hStationary : RestrictedStationaryFor integral FieldClass residual) :
    ResidualEquation residual := by
  exact separation.residual_zero_of_all_restricted_pairings_zero
    residual hStationary

/-- Restricted KG-class residual conclusion under restricted separation. -/
theorem restricted_continuum_stationary_implies_kg_residual {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (obligation : RestrictedFirstVariationObligations integral operator)
    (massSq : Real)
    (phi : ContinuumField Point)
    (hStationary :
      forall eta : ContinuumField Point,
        obligation.restricted_boundary_model.FieldClass eta ->
          FirstVariation integral operator massSq phi eta = 0) :
    ResidualEquation (Residual operator massSq phi) := by
  apply restricted_stationary_implies_residual_zero
    integral obligation.restricted_boundary_model.FieldClass
    obligation.restricted_separation
  intro eta heta
  exact hStationary eta heta

/-- Adapter condition required to recover the existing full-field route. -/
structure RestrictedToFullFirstVariationAdapter {Point : Type}
    {integral : ContinuumField Point -> Real}
    {operator : ContinuumField Point -> ContinuumField Point}
    (model : RestrictedBoundaryTermModel integral operator) where
  all_fields_in_restricted_class :
    forall f : ContinuumField Point, model.FieldClass f

/-- Full-field boundary model from a restricted model and all-fields adapter. -/
def boundaryTermModelOfRestrictedFirstVariationAdapter {Point : Type}
    {integral : ContinuumField Point -> Real}
    {operator : ContinuumField Point -> ContinuumField Point}
    (model : RestrictedBoundaryTermModel integral operator)
    (adapter : RestrictedToFullFirstVariationAdapter model) :
    BoundaryTermModel integral operator where
  boundaryTerm := model.boundaryTerm
  integration_by_parts_with_boundary := by
    intro x y
    exact model.integration_by_parts_with_boundary x y
      (adapter.all_fields_in_restricted_class x)
      (adapter.all_fields_in_restricted_class y)
  boundary_vanishes := by
    intro x y
    exact model.boundary_vanishes x y
      (adapter.all_fields_in_restricted_class x)
      (adapter.all_fields_in_restricted_class y)

/--
The existing full-field first-variation obligations are recovered only after
supplying the all-fields adapter for the restricted model.
-/
def continuumObligationsOfRestrictedFirstVariationAdapter {Point : Type}
    {integral : ContinuumField Point -> Real}
    {operator : ContinuumField Point -> ContinuumField Point}
    (obligation : RestrictedFirstVariationObligations integral operator)
    (adapter :
      RestrictedToFullFirstVariationAdapter
        obligation.restricted_boundary_model) :
    ContinuumFirstVariationObligations integral operator where
  integral_linear := obligation.integral_linear
  operator_linear := obligation.operator_linear
  boundary_model :=
    boundaryTermModelOfRestrictedFirstVariationAdapter
      obligation.restricted_boundary_model adapter
  separation := by
    refine ⟨?_⟩
    intro residual hAllPairings
    exact RestrictedSeparationPrinciple.residual_zero_of_all_restricted_pairings_zero
        obligation.restricted_separation
        residual
        (by
          intro eta heta
          exact hAllPairings eta)

/-- The existing action-shift theorem is recovered under the adapter condition. -/
theorem restricted_interface_supplies_existing_action_shift_under_adapter
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (obligation : RestrictedFirstVariationObligations integral operator)
    (adapter :
      RestrictedToFullFirstVariationAdapter
        obligation.restricted_boundary_model)
    (massSq eps : Real)
    (phi eta : ContinuumField Point) :
    ContinuumFirstVariation.Action integral operator massSq
        (VariationFamily phi eta eps) =
      ContinuumFirstVariation.Action integral operator massSq phi +
        eps * FirstVariation integral operator massSq phi eta +
        eps ^ 2 *
          ContinuumFirstVariation.Action integral operator massSq eta := by
  exact action_shift_expansion integral operator
    (continuumObligationsOfRestrictedFirstVariationAdapter obligation adapter)
    massSq eps phi eta

/-- Boundary interface for the anchored meaningful-trace restricted class. -/
def anchoredRestrictedFirstVariationBoundaryInterface
    (Point : Type) [Inhabited Point] :
    RestrictedFirstVariationBoundaryInterface
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point) where
  restricted_boundary_model := anchoredRestrictedBoundaryTermModel Point

/-- Boundary model for the anchored restricted first-variation interface. -/
def anchoredRestrictedFirstVariationBoundaryModel
    (Point : Type) [Inhabited Point] :
    RestrictedBoundaryTermModel
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point) :=
  (anchoredRestrictedFirstVariationBoundaryInterface Point).restricted_boundary_model

/-- The anchored restricted boundary interface has a nonempty field class. -/
theorem anchored_restricted_first_variation_field_class_nonempty
    {Point : Type} [Inhabited Point] :
    exists f : ContinuumField Point,
      (anchoredRestrictedFirstVariationBoundaryModel Point).FieldClass f := by
  refine ⟨@zeroField Point, ?_⟩
  change AnchoredTraceVanishingFieldClass (@zeroField Point)
  exact zero_field_in_anchored_trace_vanishing_class

/-- The anchored restricted adapter into the old full-field route is impossible. -/
theorem anchored_restricted_first_variation_adapter_impossible
    {Point : Type} [Inhabited Point] :
    Not (RestrictedToFullFirstVariationAdapter
      (anchoredRestrictedFirstVariationBoundaryModel Point)) := by
  intro adapter
  exact anchored_trace_vanishing_class_not_full (Point := Point)
    (by
      intro f
      exact adapter.all_fields_in_restricted_class f)

/-- Status readout for this bounded restricted interface attempt. -/
structure RestrictedFirstVariationInterfaceAttemptStatus where
  restricted_first_variation_interface_defined : Prop
  restricted_action_shift_expansion_discharged : Prop
  adapter_condition_recorded : Prop
  old_full_field_route_constructed : Prop
  old_full_field_route_not_constructed : Not old_full_field_route_constructed
  anchored_adapter_impossible : Prop
  nonzero_operator_green_identity_closed : Prop
  nonzero_operator_green_identity_not_closed :
    Not nonzero_operator_green_identity_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this attempt. -/
def restrictedFirstVariationInterfaceAttemptStatusV0 :
    RestrictedFirstVariationInterfaceAttemptStatus where
  restricted_first_variation_interface_defined := True
  restricted_action_shift_expansion_discharged := True
  adapter_condition_recorded := True
  old_full_field_route_constructed :=
    forall (Point : Type) [Inhabited Point],
      RestrictedToFullFirstVariationAdapter
        (anchoredRestrictedFirstVariationBoundaryModel Point)
  old_full_field_route_not_constructed := by
    intro h
    exact anchored_restricted_first_variation_adapter_impossible (h Unit)
  anchored_adapter_impossible := True
  nonzero_operator_green_identity_closed := False
  nonzero_operator_green_identity_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A4RestrictedClosedBoundaryUniverseApiRequiredId
  retained_blocker_id :=
    phase1Blocker003A2A5RestrictedFirstVariationInterfaceRetainedId
  outcome_id := restrictedFirstVariationInterfaceOutcomeId

/-- Short local status alias. -/
def restrictedFirstVariationStatusV0 :
    RestrictedFirstVariationInterfaceAttemptStatus :=
  restrictedFirstVariationInterfaceAttemptStatusV0

/-- The restricted first-variation interface is defined. -/
theorem restricted_first_variation_interface_defined_v0 :
    restrictedFirstVariationStatusV0.restricted_first_variation_interface_defined := by
  trivial

/-- Restricted algebraic action-shift expansion is discharged. -/
theorem restricted_action_shift_expansion_discharged_v0 :
    restrictedFirstVariationStatusV0.restricted_action_shift_expansion_discharged := by
  trivial

/-- The adapter condition is explicitly recorded. -/
theorem restricted_first_variation_adapter_condition_recorded_v0 :
    restrictedFirstVariationStatusV0.adapter_condition_recorded := by
  trivial

/-- The anchored adapter is impossible. -/
theorem restricted_first_variation_anchored_adapter_impossible_v0 :
    restrictedFirstVariationStatusV0.anchored_adapter_impossible := by
  trivial

/-- The old full-field route remains unconstructed. -/
theorem restricted_first_variation_old_full_route_not_constructed_v0 :
    Not restrictedFirstVariationStatusV0.old_full_field_route_constructed := by
  exact restrictedFirstVariationStatusV0.old_full_field_route_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem restricted_first_variation_nonzero_operator_green_not_closed_v0 :
    Not restrictedFirstVariationStatusV0.nonzero_operator_green_identity_closed := by
  exact restrictedFirstVariationStatusV0.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem restricted_first_variation_parent_retained_id_v0 :
    restrictedFirstVariationStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A4RestrictedClosedBoundaryUniverseApiRequiredId := by
  simp [restrictedFirstVariationStatusV0,
    restrictedFirstVariationInterfaceAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem restricted_first_variation_retained_id_v0 :
    restrictedFirstVariationStatusV0.retained_blocker_id =
      phase1Blocker003A2A5RestrictedFirstVariationInterfaceRetainedId := by
  simp [restrictedFirstVariationStatusV0,
    restrictedFirstVariationInterfaceAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem restricted_first_variation_outcome_id_v0 :
    restrictedFirstVariationStatusV0.outcome_id =
      restrictedFirstVariationInterfaceOutcomeId := by
  simp [restrictedFirstVariationStatusV0,
    restrictedFirstVariationInterfaceAttemptStatusV0]

/-- Phase 2 remains unauthorized after this bounded attempt. -/
theorem restricted_first_variation_interface_phase2_not_authorized_v0 :
    Not restrictedFirstVariationStatusV0.phase2Authorized := by
  exact restrictedFirstVariationStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained interface slice. -/
def phase1Blocker003A2A5RestrictedFirstVariationInterfaceV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a5_restricted_first_variation_v0_phase2_not_authorized :
    Not phase1Blocker003A2A5RestrictedFirstVariationInterfaceV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumRestrictedFirstVariationInterface
end QFT
end ToeFormal
