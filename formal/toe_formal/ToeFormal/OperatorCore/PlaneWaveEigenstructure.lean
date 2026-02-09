import Mathlib
import ToeFormal.OperatorCore.OperatorSignature

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ToeFormal
namespace OperatorCore

open ToeFormal.CPNLSE2D

noncomputable section

/-- Eigenvalue addition rule: if O and E are plane-wave eigen, then O+E is too, with μ+ν. -/
theorem planeWaveEigen_add
  {O E : Op2D}
  (hO : PlaneWaveEigen O)
  (hE : PlaneWaveEigen E) :
  PlaneWaveEigen (O + E) := by
  rcases hO with ⟨μ, hμ⟩
  rcases hE with ⟨ν, hν⟩
  refine ⟨fun kx ky => μ kx ky + ν kx ky, ?_⟩
  intro A kx ky
  funext x y t
  -- unfold operator addition on the nose
  simp [Op2D.instHAdd, hμ, hν, add_mul]

/--
Helper lemma: `DispersionCompatible O` pins `O` to `omega` on plane waves (as a function equality).
-/
lemma dispersionCompatible_planeWave_eq_omega
  {O : Op2D}
  (hO : DispersionCompatible O) :
  ∀ (A : ℂ) (kx ky : ℝ),
    O.Op (planeWave A kx ky)
      = (fun x y t => (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t)) := by
  rcases hO with ⟨μ, hPW, hω⟩
  intro A kx ky
  -- rewrite μ to omega using the compatibility condition
  simpa [hω kx ky] using (hPW A kx ky)

/--
Selection principle (Alternative A2):

If `O` and `(O+E)` are both dispersion-compatible, then `E` has no probe-visible effect:
it vanishes on the plane-wave probe family.

This avoids cancellation / non-vanishing assumptions about `planeWave`.
-/
theorem dispersionCompatible_add_implies_E_vanishes_on_planeWaves
  {O E : Op2D}
  (hO  : DispersionCompatible O)
  (hOE : DispersionCompatible (O + E)) :
  ∀ (A : ℂ) (kx ky : ℝ) (x y t : ℝ), E.Op (planeWave A kx ky) x y t = (0 : ℂ)
 := by
  intro A kx ky
  -- Extract the pinned-to-omega equalities on plane waves for O and O+E.
  have hOeq  := dispersionCompatible_planeWave_eq_omega (O := O) hO A kx ky
  have hOEeq := dispersionCompatible_planeWave_eq_omega (O := (O + E)) hOE A kx ky

  -- Prove pointwise (as Field2D is a function type).
  intro x y t
  have hOxy  : O.Op (planeWave A kx ky) x y t
      = (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t) := by
    simpa using congrArg (fun f => f x y t) hOeq
  have hOExy : (O + E).Op (planeWave A kx ky) x y t
      = (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t) := by
    simpa using congrArg (fun f => f x y t) hOEeq

  -- Expand (O+E).Op pointwise to O.Op + E.Op, then cancel on the left *without* dividing by planeWave.
  have hSum :
      O.Op (planeWave A kx ky) x y t + E.Op (planeWave A kx ky) x y t
        = (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t) := by
    simpa [Op2D.instHAdd] using hOExy

  have hCancel :
      (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t)
        + E.Op (planeWave A kx ky) x y t
        = (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t) := by
    -- rewrite O.Op(...) to omega*planeWave in the summed equation
    simpa [hOxy] using hSum

  -- rewrite RHS as `a + 0` so `add_left_cancel` applies
  have hCancel' :
      (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t)
        + E.Op (planeWave A kx ky) x y t
      =
      (ToeFormal.CPNLSE2D.omega kx ky : ℂ) * (planeWave A kx ky x y t) + (0 : ℂ) := by
    simpa [add_zero] using hCancel

  exact add_left_cancel hCancel'

/-- Convenience wrapper: same result as a `Field2D` equality. -/
lemma dispersionCompatible_add_implies_E_vanishes_on_planeWaves_fun
  {O E : Op2D}
  (hO  : DispersionCompatible O)
  (hOE : DispersionCompatible (O + E)) :
  ∀ (A : ℂ) (kx ky : ℝ), E.Op (planeWave A kx ky) = 0 := by
  intro A kx ky
  funext x y t
  -- reuse the pointwise theorem you already proved
  simpa using
    dispersionCompatible_add_implies_E_vanishes_on_planeWaves
      (O := O) (E := E) hO hOE A kx ky x y t

end
end OperatorCore
end ToeFormal
