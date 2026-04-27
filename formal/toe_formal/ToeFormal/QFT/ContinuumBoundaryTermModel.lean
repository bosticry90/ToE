/-
ToeFormal/QFT/ContinuumBoundaryTermModel.lean

Bounded boundary-term model for PHASE1-BLOCKER-003.

Scope:
- define a two-sided boundary trace surface for a compact-support or
  boundary-decay class
- prove the boundary flux vanishes when both field traces vanish
- instantiate `BoundaryTermModel` for a closed restricted field universe
  whose fields are all in the operator domain and compact-support/decay class
- route that boundary model into the Blocker 003 boundary sub-obligation
- keep operator-domain closure, residual separation, concrete smoothness, and
  full continuum functional analysis retained
- no Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumAnalyticBlocker003

namespace ToeFormal
namespace QFT
namespace ContinuumBoundaryTermModel

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
set_option autoImplicit false

noncomputable section

/--
Two-sided boundary trace data for a one-dimensional Green-identity style
boundary flux.  The normal-derivative traces are kept abstract; compact support
or sufficient decay will kill the flux by killing the field traces.
-/
structure TwoSidedBoundaryTrace (Point : Type) where
  leftTrace : ContinuumField Point → Real
  rightTrace : ContinuumField Point → Real
  leftNormalDerivativeTrace : ContinuumField Point → Real
  rightNormalDerivativeTrace : ContinuumField Point → Real

/-- Green-identity boundary flux for a symmetric second-order scalar operator. -/
def twoSidedBoundaryFlux {Point : Type}
    (trace : TwoSidedBoundaryTrace Point)
    (x y : ContinuumField Point) : Real :=
  (trace.rightTrace x * trace.rightNormalDerivativeTrace y -
      trace.rightTrace y * trace.rightNormalDerivativeTrace x) -
    (trace.leftTrace x * trace.leftNormalDerivativeTrace y -
      trace.leftTrace y * trace.leftNormalDerivativeTrace x)

/--
Boundary surface for a smooth compact-support or boundary-decay scalar class.

This object is still an analytic input: it supplies the Green identity and the
trace-vanishing condition for the chosen field class.  The theorem below
checks that these data instantiate the repo's `BoundaryTermModel`.
-/
structure TwoSidedCompactSupportDecayBoundarySurface {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) where
  FieldSmooth : ContinuumField Point → Prop
  CompactSupportOrBoundaryDecay : ContinuumField Point → Prop
  InOperatorDomain : ContinuumField Point → Prop
  trace : TwoSidedBoundaryTrace Point
  green_identity :
    ∀ x y : ContinuumField Point,
      InOperatorDomain x →
      InOperatorDomain y →
        ContinuumPair integral x (operator y) =
          ContinuumPair integral y (operator x) +
            twoSidedBoundaryFlux trace x y
  trace_zero_of_decay :
    ∀ f : ContinuumField Point,
      CompactSupportOrBoundaryDecay f →
        trace.leftTrace f = 0 ∧ trace.rightTrace f = 0

/--
The closed field universe needed to promote a class-restricted boundary
surface into the current unrestricted `BoundaryTermModel` API.
-/
structure ClosedCompactSupportDecayFieldUniverse {Point : Type}
    {integral : ContinuumField Point → Real}
    {operator : ContinuumField Point → ContinuumField Point}
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator) where
  all_fields_smooth :
    ∀ f : ContinuumField Point, surface.FieldSmooth f
  all_fields_decay :
    ∀ f : ContinuumField Point, surface.CompactSupportOrBoundaryDecay f
  all_fields_in_operator_domain :
    ∀ f : ContinuumField Point, surface.InOperatorDomain f

/-- Continuum assumption inventory induced by a compact-support/decay surface. -/
def assumptionInventoryOfBoundarySurface {Point : Type}
    {integral : ContinuumField Point → Real}
    {operator : ContinuumField Point → ContinuumField Point}
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator) :
    ContinuumAssumptionInventory Point where
  FieldSmooth := surface.FieldSmooth
  CompactSupportOrBoundaryDecay := surface.CompactSupportOrBoundaryDecay
  AdmissibleVariation :=
    fun eta =>
      surface.FieldSmooth eta ∧
        surface.CompactSupportOrBoundaryDecay eta ∧
          surface.InOperatorDomain eta
  InOperatorDomain := surface.InOperatorDomain
  MassOperatorSignConvention := fun _ => True

/-- The two-sided flux vanishes if both fields have vanishing boundary traces. -/
theorem two_sided_boundary_flux_vanishes_of_decay {Point : Type}
    {integral : ContinuumField Point → Real}
    {operator : ContinuumField Point → ContinuumField Point}
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator)
    (x y : ContinuumField Point)
    (hx : surface.CompactSupportOrBoundaryDecay x)
    (hy : surface.CompactSupportOrBoundaryDecay y) :
    twoSidedBoundaryFlux surface.trace x y = 0 := by
  rcases surface.trace_zero_of_decay x hx with ⟨hxLeft, hxRight⟩
  rcases surface.trace_zero_of_decay y hy with ⟨hyLeft, hyRight⟩
  simp [twoSidedBoundaryFlux, hxLeft, hxRight, hyLeft, hyRight]

/--
Instantiate the continuum `BoundaryTermModel` from a compact-support/decay
Green surface over a closed restricted field universe.
-/
def boundaryTermModelOfCompactSupportDecaySurface {Point : Type}
    {integral : ContinuumField Point → Real}
    {operator : ContinuumField Point → ContinuumField Point}
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator)
    (fieldUniverse : ClosedCompactSupportDecayFieldUniverse surface) :
    BoundaryTermModel integral operator where
  boundaryTerm := twoSidedBoundaryFlux surface.trace
  integration_by_parts_with_boundary := by
    intro x y
    exact surface.green_identity x y
      (fieldUniverse.all_fields_in_operator_domain x)
      (fieldUniverse.all_fields_in_operator_domain y)
  boundary_vanishes := by
    intro x y
    exact two_sided_boundary_flux_vanishes_of_decay surface x y
      (fieldUniverse.all_fields_decay x)
      (fieldUniverse.all_fields_decay y)

/--
Blocker 003 boundary sub-obligation supplied by the compact-support/decay
boundary model.
-/
def boundarySubObligationOfCompactSupportDecaySurface {Point : Type}
    {integral : ContinuumField Point → Real}
    {operator : ContinuumField Point → ContinuumField Point}
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator)
    (fieldUniverse : ClosedCompactSupportDecayFieldUniverse surface) :
    BoundaryTermVanishingSubObligation integral operator where
  boundary_model :=
    boundaryTermModelOfCompactSupportDecaySurface surface fieldUniverse

/--
The compact-support/decay boundary surface is enough to recover the
integration-by-parts identity used by the continuum first-variation route.
-/
theorem compact_support_decay_boundary_surface_suffices_for_ibp {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (surface :
      TwoSidedCompactSupportDecayBoundarySurface integral operator)
    (fieldUniverse : ClosedCompactSupportDecayFieldUniverse surface)
    (x y : ContinuumField Point) :
    ContinuumPair integral x (operator y) =
      ContinuumPair integral y (operator x) := by
  exact boundary_subobligation_suffices_for_integration_by_parts
    integral operator
    (boundarySubObligationOfCompactSupportDecaySurface surface fieldUniverse)
    x y

/--
Blocker 003 readout after the boundary-model surface is supplied.  It remains
conditional and keeps Phase 2 unauthorized because the other analytic
sub-obligations are still retained.
-/
def phase1Blocker003BoundaryModelV1 : Phase1Blocker003Split where
  boundaryTermVanishingStatus := .dischargedConditional
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after the boundary-model surface increment. -/
theorem phase1_blocker003_boundary_model_v1_phase2_not_authorized :
    ¬ phase1Blocker003BoundaryModelV1.phase2Authorized := by
  intro h
  exact h

end
end ContinuumBoundaryTermModel
end QFT
end ToeFormal
