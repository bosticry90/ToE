/-
ToeFormal/QFT/ScalarFirstVariation.lean

Finite/discrete scalar first-variation discharge for the strict physics lane.

Scope:
- variation object, boundary-condition object, and discrete integration-by-parts
  analogue for a finite scalar field model
- exact quadratic action expansion
- residual/operator equivalence for the finite free-scalar first variation
- no continuum KG completion, canonical master-action promotion, publication,
  submission, empirical, interacting-QFT, gauge, or Standard Model claim

This file removes one retained assumption from the bounded scalar route:
in the finite quadratic model, the first variation is not postulated. It is
derived from the exact action-shift expansion under explicit linearity and
discrete integration-by-parts hypotheses.
-/

import ToeFormal.QFT.FreeScalarDerivation

namespace ToeFormal
namespace QFT
namespace ScalarFirstVariation

open FreeScalarDerivation
open scoped BigOperators
set_option autoImplicit false

noncomputable section

/-- Pointwise addition for finite scalar fields. -/
def fieldAdd {N : Nat} (x y : ScalarField N) : ScalarField N :=
  fun i => x i + y i

/-- Pointwise scalar multiplication for finite scalar fields. -/
def fieldSMul {N : Nat} (a : Real) (x : ScalarField N) : ScalarField N :=
  fun i => a * x i

/-- A finite variation direction. -/
structure VariationObject (N : Nat) where
  direction : ScalarField N

/-- Linearity of a finite residual/kinetic operator. -/
structure DiscreteLinearOperator {N : Nat}
    (operator : ScalarField N → ScalarField N) where
  map_add :
    ∀ x y : ScalarField N,
      operator (fieldAdd x y) = fieldAdd (operator x) (operator y)
  map_smul :
    ∀ (a : Real) (x : ScalarField N),
      operator (fieldSMul a x) = fieldSMul a (operator x)

/-- Discrete integration by parts, expressed as self-adjointness of the operator. -/
structure DiscreteBoundaryCondition {N : Nat}
    (operator : ScalarField N → ScalarField N) where
  discrete_integration_by_parts :
    ∀ x y : ScalarField N, l2Pair x (operator y) = l2Pair y (operator x)

/-- Combined finite first-variation hypotheses. -/
structure FirstVariationObligationSlice {N : Nat}
    (operator : ScalarField N → ScalarField N) where
  linearity : DiscreteLinearOperator operator
  boundary : DiscreteBoundaryCondition operator

/-- Pairing is additive in its left argument. -/
theorem l2Pair_add_left {N : Nat} (x y z : ScalarField N) :
    l2Pair (fieldAdd x y) z = l2Pair x z + l2Pair y z := by
  unfold l2Pair fieldAdd
  simp [add_mul, Finset.sum_add_distrib]

/-- Pairing is additive in its right argument. -/
theorem l2Pair_add_right {N : Nat} (x y z : ScalarField N) :
    l2Pair x (fieldAdd y z) = l2Pair x y + l2Pair x z := by
  unfold l2Pair fieldAdd
  simp [mul_add, Finset.sum_add_distrib]

/-- Pairing is homogeneous in its left argument. -/
theorem l2Pair_smul_left {N : Nat} (a : Real) (x y : ScalarField N) :
    l2Pair (fieldSMul a x) y = a * l2Pair x y := by
  unfold l2Pair fieldSMul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Pairing is homogeneous in its right argument. -/
theorem l2Pair_smul_right {N : Nat} (a : Real) (x y : ScalarField N) :
    l2Pair x (fieldSMul a y) = a * l2Pair x y := by
  unfold l2Pair fieldSMul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The finite real pairing is symmetric. -/
theorem l2Pair_comm {N : Nat} (x y : ScalarField N) :
    l2Pair x y = l2Pair y x := by
  unfold l2Pair
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Free scalar residual for a finite kinetic operator plus mass term. -/
def FreeScalarResidual {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real)
    (phi : ScalarField N) : ScalarField N :=
  fieldAdd (operator phi) (fieldSMul massSq phi)

/-- Finite quadratic free-scalar action. -/
def FreeScalarAction {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real)
    (phi : ScalarField N) : Real :=
  (1 / 2 : Real) * l2Pair phi (operator phi) +
    (1 / 2 : Real) * massSq * l2Pair phi phi

/-- First variation candidate, later derived as the linear coefficient. -/
def FirstVariation {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real)
    (phi eta : ScalarField N) : Real :=
  l2Pair eta (FreeScalarResidual operator massSq phi)

/-- Residual/operator equivalence for the finite first variation. -/
theorem residual_pair_eq {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real)
    (phi eta : ScalarField N) :
    FirstVariation operator massSq phi eta =
      l2Pair eta (operator phi) + massSq * l2Pair eta phi := by
  unfold FirstVariation FreeScalarResidual
  rw [l2Pair_add_right, l2Pair_smul_right]

/-- Exact expansion of the mass quadratic term under a finite variation. -/
theorem mass_pair_shift_expansion {N : Nat}
    (eps : Real) (phi eta : ScalarField N) :
    l2Pair (fieldAdd phi (fieldSMul eps eta))
        (fieldAdd phi (fieldSMul eps eta)) =
      l2Pair phi phi + 2 * eps * l2Pair eta phi +
        eps ^ 2 * l2Pair eta eta := by
  rw [l2Pair_add_left, l2Pair_add_right, l2Pair_smul_right, l2Pair_smul_left,
    l2Pair_add_right, l2Pair_smul_right]
  rw [l2Pair_comm phi eta]
  ring

/--
Exact expansion of the kinetic quadratic term. The only boundary input is the
finite discrete-integration-by-parts/self-adjointness condition.
-/
theorem kinetic_pair_shift_expansion {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (hLinear : DiscreteLinearOperator operator)
    (hBoundary : DiscreteBoundaryCondition operator)
    (eps : Real) (phi eta : ScalarField N) :
    l2Pair (fieldAdd phi (fieldSMul eps eta))
        (operator (fieldAdd phi (fieldSMul eps eta))) =
      l2Pair phi (operator phi) +
        2 * eps * l2Pair eta (operator phi) +
        eps ^ 2 * l2Pair eta (operator eta) := by
  rw [hLinear.map_add, hLinear.map_smul]
  rw [l2Pair_add_left, l2Pair_add_right, l2Pair_smul_right, l2Pair_smul_left,
    l2Pair_add_right, l2Pair_smul_right]
  rw [hBoundary.discrete_integration_by_parts phi eta]
  ring

/--
Finite first-variation discharge: the exact action shift has linear
coefficient equal to pairing with the free scalar residual.
-/
theorem action_shift_expansion {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (obligation : FirstVariationObligationSlice operator)
    (massSq eps : Real)
    (phi eta : ScalarField N) :
    FreeScalarAction operator massSq (fieldAdd phi (fieldSMul eps eta)) =
      FreeScalarAction operator massSq phi +
        eps * FirstVariation operator massSq phi eta +
        eps ^ 2 * FreeScalarAction operator massSq eta := by
  unfold FreeScalarAction
  rw [kinetic_pair_shift_expansion operator obligation.linearity obligation.boundary eps phi eta]
  rw [mass_pair_shift_expansion eps phi eta]
  rw [residual_pair_eq operator massSq phi eta]
  ring

/-- The finite first variation directly supplies a master-action scalar slice. -/
def masterActionScalarSliceFromQuadratic
    {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real) :
    MasterActionScalarSlice N where
  boxPlusMass := FreeScalarResidual operator massSq
  firstVariation := FirstVariation operator massSq
  firstVariation_matches_boxPlusMass := by
    intro phi eta
    rfl

/--
Stationarity of the finite quadratic action's derived first variation implies
the free-scalar/KG residual equation.
-/
theorem finite_quadratic_stationary_implies_kg
    {N : Nat}
    (operator : ScalarField N → ScalarField N)
    (massSq : Real)
    (phi : ScalarField N)
    (hStationary :
      ∀ eta : ScalarField N, FirstVariation operator massSq phi eta = 0) :
    KleinGordonEquation (FreeScalarResidual operator massSq) phi := by
  exact master_action_stationary_implies_free_scalar_kg
    (masterActionScalarSliceFromQuadratic operator massSq)
    phi
    hStationary

end
end ScalarFirstVariation
end QFT
end ToeFormal
