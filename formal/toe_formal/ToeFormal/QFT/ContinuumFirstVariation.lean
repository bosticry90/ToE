/-
ToeFormal/QFT/ContinuumFirstVariation.lean

Continuum first-variation theorem target for the strict physics lane.

Scope:
- continuum-facing field, variation, pairing, action, and residual objects
- named assumption inventory for smoothness, boundary decay, admissible
  variations, operator domain, and mass/operator sign convention
- boundary-term lemma isolating integration by parts as the decisive analytic
  step
- algebraic first-variation theorem conditional on linear integral, linear
  operator, boundary vanishing, and separation assumptions
- no continuum KG completion, canonical master-action promotion, publication,
  empirical, interacting-QFT, gauge, or Standard Model claim

This file does not pretend the functional analysis is solved. It makes the
continuum lift precise: the algebraic route is mechanically checked, while the
analytic assumptions remain explicit retained blockers.
-/

import Mathlib

namespace ToeFormal
namespace QFT
namespace ContinuumFirstVariation

set_option autoImplicit false

noncomputable section

/-- Continuum-facing real scalar fields over an abstract point space. -/
abbrev ContinuumField (Point : Type) := Point → Real

/-- Pointwise addition for continuum fields. -/
def fieldAdd {Point : Type}
    (x y : ContinuumField Point) : ContinuumField Point :=
  fun p => x p + y p

/-- Pointwise scalar multiplication for continuum fields. -/
def fieldSMul {Point : Type}
    (a : Real) (x : ContinuumField Point) : ContinuumField Point :=
  fun p => a * x p

/-- One-parameter variation family `phi + eps eta`. -/
def VariationFamily {Point : Type}
    (phi eta : ContinuumField Point) (eps : Real) : ContinuumField Point :=
  fieldAdd phi (fieldSMul eps eta)

/-- Abstract continuum pairing; `integral` supplies the analytic integration model. -/
def ContinuumPair {Point : Type}
    (integral : ContinuumField Point → Real)
    (x y : ContinuumField Point) : Real :=
  integral (fun p => x p * y p)

/-- Inventory of continuum assumptions needed before the target becomes unconditional. -/
structure ContinuumAssumptionInventory (Point : Type) where
  FieldSmooth : ContinuumField Point → Prop
  CompactSupportOrBoundaryDecay : ContinuumField Point → Prop
  AdmissibleVariation : ContinuumField Point → Prop
  InOperatorDomain : ContinuumField Point → Prop
  MassOperatorSignConvention : Real → Prop

/-- Field/variation witness package for the assumption inventory. -/
structure ContinuumAssumptionWitness {Point : Type}
    (inventory : ContinuumAssumptionInventory Point)
    (massSq : Real)
    (phi eta : ContinuumField Point) where
  phi_smooth : inventory.FieldSmooth phi
  eta_smooth : inventory.FieldSmooth eta
  eta_admissible : inventory.AdmissibleVariation eta
  phi_domain : inventory.InOperatorDomain phi
  eta_domain : inventory.InOperatorDomain eta
  phi_boundary : inventory.CompactSupportOrBoundaryDecay phi
  eta_boundary : inventory.CompactSupportOrBoundaryDecay eta
  mass_sign : inventory.MassOperatorSignConvention massSq

/-- Linearity of the continuum integration model. -/
structure LinearIntegral {Point : Type}
    (integral : ContinuumField Point → Real) where
  map_add :
    ∀ f g : ContinuumField Point,
      integral (fun p => f p + g p) = integral f + integral g
  map_smul :
    ∀ (a : Real) (f : ContinuumField Point),
      integral (fun p => a * f p) = a * integral f

/-- Linearity of the continuum kinetic/residual operator. -/
structure LinearOperator {Point : Type}
    (operator : ContinuumField Point → ContinuumField Point) where
  map_add :
    ∀ x y : ContinuumField Point,
      operator (fieldAdd x y) = fieldAdd (operator x) (operator y)
  map_smul :
    ∀ (a : Real) (x : ContinuumField Point),
      operator (fieldSMul a x) = fieldSMul a (operator x)

/--
Integration by parts with an explicit boundary term, plus the retained
assumption that the boundary term vanishes on the admitted field class.
-/
structure BoundaryTermModel {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) where
  boundaryTerm : ContinuumField Point → ContinuumField Point → Real
  integration_by_parts_with_boundary :
    ∀ x y : ContinuumField Point,
      ContinuumPair integral x (operator y) =
        ContinuumPair integral y (operator x) + boundaryTerm x y
  boundary_vanishes :
    ∀ x y : ContinuumField Point, boundaryTerm x y = 0

/-- Continuum separation principle: zero pairing against all variations kills the residual. -/
structure SeparationPrinciple {Point : Type}
    (integral : ContinuumField Point → Real) where
  residual_zero_of_all_pairings_zero :
    ∀ residual : ContinuumField Point,
      (∀ eta : ContinuumField Point, ContinuumPair integral eta residual = 0) →
        residual = 0

/-- Bundle of analytic obligations for the continuum first-variation route. -/
structure ContinuumFirstVariationObligations {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) where
  integral_linear : LinearIntegral integral
  operator_linear : LinearOperator operator
  boundary_model : BoundaryTermModel integral operator
  separation : SeparationPrinciple integral

/-- Boundary-term lemma: vanishing boundary term gives the integration-by-parts identity. -/
theorem continuum_integration_by_parts_from_boundary_vanishing {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (hBoundary : BoundaryTermModel integral operator)
    (x y : ContinuumField Point) :
    ContinuumPair integral x (operator y) =
      ContinuumPair integral y (operator x) := by
  rw [hBoundary.integration_by_parts_with_boundary]
  rw [hBoundary.boundary_vanishes]
  ring

/-- Continuum pairing is additive in its left argument under linear integration. -/
theorem pair_add_left {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (x y z : ContinuumField Point) :
    ContinuumPair integral (fieldAdd x y) z =
      ContinuumPair integral x z + ContinuumPair integral y z := by
  unfold ContinuumPair fieldAdd
  rw [← hIntegral.map_add]
  congr
  funext p
  ring

/-- Continuum pairing is additive in its right argument under linear integration. -/
theorem pair_add_right {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (x y z : ContinuumField Point) :
    ContinuumPair integral x (fieldAdd y z) =
      ContinuumPair integral x y + ContinuumPair integral x z := by
  unfold ContinuumPair fieldAdd
  rw [← hIntegral.map_add]
  congr
  funext p
  ring

/-- Continuum pairing is homogeneous in its left argument under linear integration. -/
theorem pair_smul_left {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (a : Real) (x y : ContinuumField Point) :
    ContinuumPair integral (fieldSMul a x) y =
      a * ContinuumPair integral x y := by
  unfold ContinuumPair fieldSMul
  rw [← hIntegral.map_smul]
  congr
  funext p
  ring

/-- Continuum pairing is homogeneous in its right argument under linear integration. -/
theorem pair_smul_right {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (a : Real) (x y : ContinuumField Point) :
    ContinuumPair integral x (fieldSMul a y) =
      a * ContinuumPair integral x y := by
  unfold ContinuumPair fieldSMul
  rw [← hIntegral.map_smul]
  congr
  funext p
  ring

/-- The continuum real pairing is symmetric at the pointwise-integrand level. -/
theorem pair_comm {Point : Type}
    (integral : ContinuumField Point → Real)
    (x y : ContinuumField Point) :
    ContinuumPair integral x y = ContinuumPair integral y x := by
  unfold ContinuumPair
  congr
  funext p
  ring

/-- Continuum free scalar residual for an operator plus mass term. -/
def Residual {Point : Type}
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi : ContinuumField Point) : ContinuumField Point :=
  fieldAdd (operator phi) (fieldSMul massSq phi)

/-- Continuum quadratic scalar action target. -/
def Action {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi : ContinuumField Point) : Real :=
  (1 / 2 : Real) * ContinuumPair integral phi (operator phi) +
    (1 / 2 : Real) * massSq * ContinuumPair integral phi phi

/-- Continuum first variation as residual pairing. -/
def FirstVariation {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi eta : ContinuumField Point) : Real :=
  ContinuumPair integral eta (Residual operator massSq phi)

/-- Stationarity against all continuum variations. -/
def StationaryFor {Point : Type}
    (integral : ContinuumField Point → Real)
    (residual : ContinuumField Point) : Prop :=
  ∀ eta : ContinuumField Point, ContinuumPair integral eta residual = 0

/-- Continuum residual equation target. -/
def ResidualEquation {Point : Type} (residual : ContinuumField Point) : Prop :=
  residual = 0

/-- Algebraic quadratic expansion around a base value. -/
def HasQuadraticExpansionAtBase
    (path : Real → Real) (base derivative quadratic : Real) : Prop :=
  ∀ eps : Real, path eps = base + eps * derivative + eps ^ 2 * quadratic

/-- Algebraic derivative-at-zero target, with a visible quadratic remainder. -/
def HasAlgebraicDerivativeAtZero
    (path : Real → Real) (base derivative : Real) : Prop :=
  ∃ quadratic : Real, HasQuadraticExpansionAtBase path base derivative quadratic

/-- Residual-pairing equivalence for the continuum first variation. -/
theorem residual_pair_eq {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi eta : ContinuumField Point) :
    FirstVariation integral operator massSq phi eta =
      ContinuumPair integral eta (operator phi) +
        massSq * ContinuumPair integral eta phi := by
  unfold FirstVariation Residual
  rw [pair_add_right integral hIntegral, pair_smul_right integral hIntegral]

/-- Exact expansion of the continuum mass quadratic term. -/
theorem mass_pair_shift_expansion {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (eps : Real)
    (phi eta : ContinuumField Point) :
    ContinuumPair integral (fieldAdd phi (fieldSMul eps eta))
        (fieldAdd phi (fieldSMul eps eta)) =
      ContinuumPair integral phi phi +
        2 * eps * ContinuumPair integral eta phi +
        eps ^ 2 * ContinuumPair integral eta eta := by
  rw [pair_add_left integral hIntegral, pair_add_right integral hIntegral]
  rw [pair_smul_right integral hIntegral, pair_smul_left integral hIntegral]
  rw [pair_add_right integral hIntegral, pair_smul_right integral hIntegral]
  rw [pair_comm integral phi eta]
  ring

/-- Exact expansion of the continuum kinetic quadratic term. -/
theorem kinetic_pair_shift_expansion {Point : Type}
    (integral : ContinuumField Point → Real)
    (hIntegral : LinearIntegral integral)
    (operator : ContinuumField Point → ContinuumField Point)
    (hLinear : LinearOperator operator)
    (hBoundary : BoundaryTermModel integral operator)
    (eps : Real)
    (phi eta : ContinuumField Point) :
    ContinuumPair integral (fieldAdd phi (fieldSMul eps eta))
        (operator (fieldAdd phi (fieldSMul eps eta))) =
      ContinuumPair integral phi (operator phi) +
        2 * eps * ContinuumPair integral eta (operator phi) +
        eps ^ 2 * ContinuumPair integral eta (operator eta) := by
  rw [hLinear.map_add, hLinear.map_smul]
  rw [pair_add_left integral hIntegral, pair_add_right integral hIntegral]
  rw [pair_smul_right integral hIntegral, pair_smul_left integral hIntegral]
  rw [pair_add_right integral hIntegral, pair_smul_right integral hIntegral]
  rw [continuum_integration_by_parts_from_boundary_vanishing
    integral operator hBoundary phi eta]
  ring

/--
Continuum first-variation target: the action shift has linear coefficient equal
to residual pairing, conditional on the retained analytic obligations.
-/
theorem action_shift_expansion {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (obligation : ContinuumFirstVariationObligations integral operator)
    (massSq eps : Real)
    (phi eta : ContinuumField Point) :
    Action integral operator massSq (VariationFamily phi eta eps) =
      Action integral operator massSq phi +
        eps * FirstVariation integral operator massSq phi eta +
        eps ^ 2 * Action integral operator massSq eta := by
  unfold Action VariationFamily
  rw [kinetic_pair_shift_expansion
    integral obligation.integral_linear
    operator obligation.operator_linear obligation.boundary_model eps phi eta]
  rw [mass_pair_shift_expansion integral obligation.integral_linear eps phi eta]
  rw [residual_pair_eq integral obligation.integral_linear operator massSq phi eta]
  ring

/-- Algebraic derivative-at-zero statement for the continuum scalar action target. -/
theorem action_has_algebraic_derivative_at_zero {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (obligation : ContinuumFirstVariationObligations integral operator)
    (massSq : Real)
    (phi eta : ContinuumField Point) :
    HasAlgebraicDerivativeAtZero
      (fun eps => Action integral operator massSq (VariationFamily phi eta eps))
      (Action integral operator massSq phi)
      (FirstVariation integral operator massSq phi eta) := by
  refine ⟨Action integral operator massSq eta, ?_⟩
  intro eps
  exact action_shift_expansion integral operator obligation massSq eps phi eta

/-- Stationarity plus the separation principle implies the residual equation. -/
theorem stationary_implies_residual_zero {Point : Type}
    (integral : ContinuumField Point → Real)
    (separation : SeparationPrinciple integral)
    (residual : ContinuumField Point)
    (hStationary : StationaryFor integral residual) :
    ResidualEquation residual := by
  exact separation.residual_zero_of_all_pairings_zero residual hStationary

/--
Continuum KG-class residual conclusion, conditional on the retained analytic
obligations and stationarity of the derived first variation.
-/
theorem continuum_stationary_implies_kg_residual {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (obligation : ContinuumFirstVariationObligations integral operator)
    (massSq : Real)
    (phi : ContinuumField Point)
    (hStationary :
      ∀ eta : ContinuumField Point,
        FirstVariation integral operator massSq phi eta = 0) :
    ResidualEquation (Residual operator massSq phi) := by
  apply stationary_implies_residual_zero integral obligation.separation
  intro eta
  exact hStationary eta

end
end ContinuumFirstVariation
end QFT
end ToeFormal
