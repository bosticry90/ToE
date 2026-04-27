/-
ToeFormal/QFT/FreeScalarDerivation.lean

Strict physics derivation surface for the bounded free-scalar route.

Scope:
- finite-dimensional test-field model for the free scalar residual
- no publication-package, submission-readiness, or manuscript claim
- no canonical master-action promotion
- no interacting QFT, gauge, Standard Model, or global ToE closure claim

The core theorem is intentionally narrow: if the scalar slice first variation
matches the box-plus-mass residual against every test variation, stationarity
forces the residual to vanish. Continuum regularity, boundary discharge, and
scalar-slice extraction remain explicit analytic obligations outside this file.
-/

import Mathlib

namespace ToeFormal
namespace QFT
namespace FreeScalarDerivation

noncomputable section
open scoped BigOperators
set_option autoImplicit false

/-- Bounded real scalar fields over `N` test degrees of freedom. -/
abbrev ScalarField (N : Nat) := Fin N → Real

/-- Finite test-pairing used to separate scalar residual components. -/
def l2Pair {N : Nat} (eta psi : ScalarField N) : Real :=
  ∑ i, eta i * psi i

/-- Stationarity against all finite test variations for a residual operator. -/
def StationaryFor
    {N : Nat} (operator : ScalarField N → ScalarField N) (phi : ScalarField N) :
    Prop :=
  ∀ eta : ScalarField N, l2Pair eta (operator phi) = 0

/-- Free-scalar/Klein-Gordon-class residual equation in the bounded model. -/
def KleinGordonEquation
    {N : Nat} (boxPlusMass : ScalarField N → ScalarField N) (phi : ScalarField N) :
    Prop :=
  boxPlusMass phi = 0

/-- Pointwise addition for scalar residuals. -/
def addField {N : Nat} (x y : ScalarField N) : ScalarField N :=
  fun i => x i + y i

/-- General scalar residual before free-field specialization. -/
def InteractingScalarResidual {N : Nat}
    (boxPlusMass interactionDerivative : ScalarField N → ScalarField N)
    (phi : ScalarField N) : ScalarField N :=
  addField (boxPlusMass phi) (interactionDerivative phi)

/-- Explicit free-field regime: the interaction derivative vanishes. -/
def FreeFieldRegime {N : Nat}
    (interactionDerivative : ScalarField N → ScalarField N)
    (phi : ScalarField N) : Prop :=
  interactionDerivative phi = 0

/--
Scalar slice of the candidate master action, reduced to the exact analytic
obligation needed by this file: the first variation must pair each admissible
test variation with the box-plus-mass residual.
-/
structure MasterActionScalarSlice (N : Nat) where
  boxPlusMass : ScalarField N → ScalarField N
  firstVariation : ScalarField N → ScalarField N → Real
  firstVariation_matches_boxPlusMass :
    ∀ phi eta : ScalarField N, firstVariation phi eta = l2Pair eta (boxPlusMass phi)

/-- Stationarity of the scalar slice first variation. -/
def MasterActionStationary {N : Nat}
    (slice : MasterActionScalarSlice N) (phi : ScalarField N) : Prop :=
  ∀ eta : ScalarField N, slice.firstVariation phi eta = 0

/--
Finite separating-variation theorem.

This replaces a scaffold token with a real proof: if every test variation pairs
to zero with a residual, every residual component is zero.
-/
theorem stationary_implies_operator_zero
    {N : Nat} (operator : ScalarField N → ScalarField N) (phi : ScalarField N)
    (hStationary : StationaryFor operator phi) :
    operator phi = 0 := by
  funext i
  have htest := hStationary (fun j => if j = i then operator phi i else 0)
  unfold l2Pair at htest
  have hsumeq :
      (∑ j : Fin N, (if j = i then operator phi i else 0) * operator phi j) =
        operator phi i * operator phi i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _hb hbi
      simp [hbi]
    · intro hi
      simp at hi
  have hsq : operator phi i * operator phi i = 0 := by
    simpa [hsumeq] using htest
  exact mul_self_eq_zero.mp hsq

/-- Stationarity against all test variations implies the KG-class residual equation. -/
theorem stationary_implies_kg
    {N : Nat} (boxPlusMass : ScalarField N → ScalarField N) (phi : ScalarField N)
    (hStationary : StationaryFor boxPlusMass phi) :
    KleinGordonEquation boxPlusMass phi := by
  unfold KleinGordonEquation
  exact stationary_implies_operator_zero boxPlusMass phi hStationary

/--
Master-action scalar-slice theorem.

Once the scalar slice first-variation formula is discharged, stationarity gives
the bounded free-scalar/KG-class equation directly.
-/
theorem master_action_stationary_implies_free_scalar_kg
    {N : Nat} (slice : MasterActionScalarSlice N) (phi : ScalarField N)
    (hStationary : MasterActionStationary slice phi) :
    KleinGordonEquation slice.boxPlusMass phi := by
  apply stationary_implies_kg
  intro eta
  have h := hStationary eta
  rw [slice.firstVariation_matches_boxPlusMass phi eta] at h
  exact h

/-- In the free-field regime, the interacting residual collapses to the KG residual. -/
theorem free_field_residual_eq_boxPlusMass
    {N : Nat}
    (boxPlusMass interactionDerivative : ScalarField N → ScalarField N)
    (phi : ScalarField N)
    (hFree : FreeFieldRegime interactionDerivative phi) :
    InteractingScalarResidual boxPlusMass interactionDerivative phi = boxPlusMass phi := by
  funext i
  have hPoint := congrFun hFree i
  simp [InteractingScalarResidual, addField, hPoint]

/--
If the general scalar residual is stationary and the interaction derivative is
zero, stationarity discharges the free scalar/KG residual.
-/
theorem interacting_stationary_in_free_regime_implies_kg
    {N : Nat}
    (boxPlusMass interactionDerivative : ScalarField N → ScalarField N)
    (phi : ScalarField N)
    (hFree : FreeFieldRegime interactionDerivative phi)
    (hStationary :
      StationaryFor (InteractingScalarResidual boxPlusMass interactionDerivative) phi) :
    KleinGordonEquation boxPlusMass phi := by
  apply stationary_implies_kg
  intro eta
  have h := hStationary eta
  rw [free_field_residual_eq_boxPlusMass boxPlusMass interactionDerivative phi hFree] at h
  exact h

/-- Local scalar Lagrangian density terms after time/space split. -/
def FreeScalarLagrangian (dtPhi gradNormSq massSq phi interaction : Real) : Real :=
  (1 / 2 : Real) * dtPhi ^ 2 - (1 / 2 : Real) * gradNormSq -
    (1 / 2 : Real) * massSq * phi ^ 2 - interaction

/-- Canonical momentum for the free scalar time-derivative term. -/
def CanonicalMomentum (dtPhi : Real) : Real := dtPhi

/-- Legendre-transform Hamiltonian density from a scalar Lagrangian density. -/
def LegendreHamiltonian (pi dtPhi gradNormSq massSq phi interaction : Real) : Real :=
  pi * dtPhi - FreeScalarLagrangian dtPhi gradNormSq massSq phi interaction

/-- The scalar Legendre transform gives the standard positive quadratic Hamiltonian form. -/
theorem legendre_transform_with_canonical_momentum
    (dtPhi gradNormSq massSq phi interaction : Real) :
    LegendreHamiltonian (CanonicalMomentum dtPhi) dtPhi gradNormSq massSq phi interaction =
      (1 / 2 : Real) * dtPhi ^ 2 + (1 / 2 : Real) * gradNormSq +
        (1 / 2 : Real) * massSq * phi ^ 2 + interaction := by
  unfold LegendreHamiltonian CanonicalMomentum FreeScalarLagrangian
  ring

/--
Exact algebraic identity behind the nonrelativistic envelope expansion:
`omega = m + eps` and `omega^2 = m^2 + k^2` imply
`2 m eps + eps^2 = k^2`.
-/
theorem kg_dispersion_envelope_identity
    (m k eps : Real)
    (hDispersion : (m + eps) ^ 2 = m ^ 2 + k ^ 2) :
    2 * m * eps + eps ^ 2 = k ^ 2 := by
  nlinarith [hDispersion]

/--
Schrodinger-class leading term under an explicit zero-remainder assumption.
The dropped quadratic envelope remainder is therefore visible in the theorem
statement rather than hidden in prose.
-/
theorem kg_dispersion_to_schrodinger_when_quadratic_remainder_zero
    (m k eps : Real)
    (hm : m ≠ 0)
    (hDispersion : (m + eps) ^ 2 = m ^ 2 + k ^ 2)
    (hRemainder : eps ^ 2 = 0) :
    eps = k ^ 2 / (2 * m) := by
  have hident : 2 * m * eps + eps ^ 2 = k ^ 2 :=
    kg_dispersion_envelope_identity m k eps hDispersion
  have hlinear : 2 * m * eps = k ^ 2 := by
    nlinarith
  field_simp [hm] at hlinear ⊢
  nlinarith

end
end FreeScalarDerivation
end QFT
end ToeFormal
