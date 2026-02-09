/-
ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean

Phase A3 (axiom quarantine):
- Contains ONLY the operator-action axioms on the plane-wave probe family.

Everything else (definitions, lemmas, theorems) should live outside this file.

Axioms (probe-relative):
- Dt planeWave = (-i * omega) * planeWave
- Delta planeWave = (-(kx^2 + ky^2)) * planeWave
-/
import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

/-- Axiom: closed form of Dt acting on the plane-wave probe family. -/
axiom Dt_planeWave (A : ℂ) (kx ky : ℝ) :
  Dt (planeWave A kx ky)
    =
    fun x y t =>
      (-Complex.I * ((omega kx ky : ℂ))) * (planeWave A kx ky x y t)

/-- Axiom: closed form of Delta acting on the plane-wave probe family. -/
axiom Delta_planeWave (A : ℂ) (kx ky : ℝ) :
  Delta (planeWave A kx ky)
    =
    fun x y t =>
      (-((kx ^ 2 + ky ^ 2 : ℝ) : ℂ)) * (planeWave A kx ky x y t)

end
end CPNLSE2D
end ToeFormal
