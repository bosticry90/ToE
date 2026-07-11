/-
This proof variant was produced by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
Project request UUID: 3fc6de82-1391-4c5e-a661-a128954e18d1

The original file repeated the complete canonical dispersion API under the
same namespace, so it could compile alone but could not be imported together
with `ToeFormal.CPNLSE2D.Dispersion`.  This integrated form preserves the
independent proof witness and provenance while using the canonical API.
-/

import ToeFormal.CPNLSE2D.Dispersion

namespace ToeFormal
namespace CPNLSE2D
namespace DispersionAristotle

noncomputable section
set_option autoImplicit false

/-- Aristotle-path recheck of the locked two-dimensional dispersion formula. -/
theorem omega_recheck (kx ky : ℝ) :
    omega kx ky = (kx ^ 2 + ky ^ 2) / 2 := by
  exact omega_expand kx ky

/-- Aristotle-path recheck of the canonical structural plane-wave template. -/
theorem planeWave_recheck (A : ℂ) (kx ky : ℝ) :
    planeWave A kx ky =
      fun (x y t : ℝ) =>
        A * Complex.exp (Complex.I * ((kx * x + ky * y - (omega kx ky) * t) : ℂ)) := by
  rfl

end


end DispersionAristotle
end CPNLSE2D
end ToeFormal
