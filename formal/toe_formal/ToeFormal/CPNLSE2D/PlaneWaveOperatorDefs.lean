/-
ToeFormal/CPNLSE2D/PlaneWaveOperatorDefs.lean

Phase A3 (definitions only):
- Opaque operators on Field2D.
- Structural definitions: Delta, L, EQ02Holds, eigC.
- No axioms, no theorems.

This file is intended to be imported both by the axiom quarantine file
and by theorem modules.

Scope:
- Structural-only. No physical claims.
- No analytic development of derivatives in Mathlib.
- Reuses Field2D and planeWave from ToeFormal.CPNLSE2D.Dispersion.
-/
import Mathlib
import ToeFormal.CPNLSE2D.Dispersion

namespace ToeFormal
namespace CPNLSE2D

noncomputable section
set_option autoImplicit false

/-- Time-derivative operator (opaque). -/
opaque Dt : Field2D → Field2D

/-- Second x-derivative operator (opaque). -/
opaque Dxx : Field2D → Field2D

/-- Second y-derivative operator (opaque). -/
opaque Dyy : Field2D → Field2D

/-- Laplacian operator as the sum of second derivatives (structural definition). -/
def Delta (ψ : Field2D) : Field2D :=
  fun x y t => Dxx ψ x y t + Dyy ψ x y t

/-- Linear spatial operator L := - (1/2) * Delta (structural definition). -/
def L (ψ : Field2D) : Field2D :=
  fun x y t => (-(1 : ℂ) / 2) * (Delta ψ x y t)

/--
EQ-02 holds for ψ as a pointwise operator identity:
  i * Dt ψ = - (1/2) * Delta ψ
-/
def EQ02Holds (ψ : Field2D) : Prop :=
  ∀ x y t : ℝ,
    Complex.I * (Dt ψ x y t) = (-(1 : ℂ) / 2) * (Delta ψ x y t)

/-- Complex eigenvalue coefficient: ((kx^2 + ky^2) : ℝ) coerced to ℂ, divided by 2 in ℂ. -/
def eigC (kx ky : ℝ) : ℂ :=
  (((kx ^ 2 + ky ^ 2 : ℝ) : ℂ) / 2)

end
end CPNLSE2D
end ToeFormal
