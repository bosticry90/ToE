/-
ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

Phase B: Structural lemma for dispersion preservation under admissible perturbations.

Scope:
- Structural-only. No physical claims.
- No analytic linearization, no Fréchet derivatives.
- Uses the operator-axiom layer from PlaneWaveOperators.lean.

Idea:
- A perturbation P preserves DR-01 (on the plane-wave probe) if it contributes
  nothing to the planeWave mode in the linear regime probe used for DR-01.

This is the minimal Lean formalization consistent with the current framework:
- We can’t talk about "linear part at ψ=0" analytically,
  so we encode a sufficient structural condition on the specific probe family.
-/
import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperators

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

/-- A perturbation term: abstract operator on Field2D. -/
abbrev Perturbation := Field2D → Field2D

/-
Modified EQ-02 (with perturbation):
  i * Dt ψ = -(1/2) * Delta ψ + P ψ
written pointwise.
-/
def EQ02PertHolds (P : Perturbation) (ψ : Field2D) : Prop :=
  ∀ x y t : ℝ,
    Complex.I * (Dt ψ x y t)
      =
    (-(1 : ℂ) / 2) * (Delta ψ x y t) + (P ψ x y t)

/-
Phase-B admissibility predicate (structural substitute for "no linear part at ψ=0"):

On the DR-01 probe family `planeWave`, the perturbation contributes zero.

This is deliberately *probe-relative*:
- It is the strongest claim we can make without analytic linearization,
  yet it is exactly what is needed to show DR-01 coefficient-equality is unchanged
  at the plane-wave test level.
-/
def AdmissibleOnPlaneWave (P : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ) (x y t : ℝ),
    P (planeWave A kx ky) x y t = 0

/-
Main Phase-B lemma:
If P is admissible on the planeWave probe family, then the perturbed EQ-02 on planeWave
reduces to the same coefficient-equality-times-planeWave form as the unperturbed EQ-02.

No cancellation of planeWave is performed.
-/
theorem EQ02Pert_planeWave_reduces_to_same_coeff_equality
  (P : Perturbation) (hP : AdmissibleOnPlaneWave P)
  (A : ℂ) (kx ky : ℝ) :
  EQ02PertHolds P (planeWave A kx ky)
    ↔
  (∀ x y t : ℝ,
      ((omega kx ky : ℂ)) * (planeWave A kx ky x y t)
        =
      (eigC kx ky) * (planeWave A kx ky x y t)) := by
  constructor
  · intro h x y t
    have hxy := h x y t
    -- closed forms from A3
    have hL := congrArg (fun f => f x y t) (iDt_planeWave_closed A kx ky)
    have hR := congrArg (fun f => f x y t) (negHalfDelta_planeWave_closed A kx ky)
    -- use admissibility to drop P term
    have hPx : P (planeWave A kx ky) x y t = 0 := hP A kx ky x y t
    calc
      (omega kx ky : ℂ) * (planeWave A kx ky x y t)
          = Complex.I * (Dt (planeWave A kx ky) x y t) := by
              exact Eq.symm hL
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) + (P (planeWave A kx ky) x y t) := hxy
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) := by simp [hPx]
      _ = (eigC kx ky) * (planeWave A kx ky x y t) := hR
  · intro h x y t
    -- closed forms from A3
    have hEq := h x y t
    have hL := congrArg (fun f => f x y t) (iDt_planeWave_closed A kx ky)
    have hR := congrArg (fun f => f x y t) (negHalfDelta_planeWave_closed A kx ky)
    have hPx : P (planeWave A kx ky) x y t = 0 := hP A kx ky x y t
    calc
      Complex.I * (Dt (planeWave A kx ky) x y t)
          = (omega kx ky : ℂ) * (planeWave A kx ky x y t) := hL
      _ = (eigC kx ky) * (planeWave A kx ky x y t) := hEq
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) := by
            exact Eq.symm hR
      _ = (-(1 : ℂ) / 2) * (Delta (planeWave A kx ky) x y t) + (P (planeWave A kx ky) x y t) := by
            simp [hPx]

end

end CPNLSE2D
end ToeFormal
