import Mathlib
import ToeFormal.CPNLSE2D.Dispersion

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ToeFormal
namespace OperatorCore

open Complex

noncomputable section

-- Reuse your canonical Field2D and planeWave
open ToeFormal.CPNLSE2D

/-- An abstract 2D field operator. -/
structure Op2D where
  Op : Field2D → Field2D

namespace Op2D

/-- Pointwise addition of operators. -/
instance : HAdd Op2D Op2D Op2D where
  hAdd A B := ⟨fun ψ => fun x y t => (A.Op ψ x y t) + (B.Op ψ x y t)⟩

/-- Zero operator. -/
instance : OfNat Op2D 0 where
  ofNat := ⟨fun _ψ => fun _x _y _t => 0⟩

end Op2D

/--
Plane-wave eigen-closure: there exists an eigenvalue map μ(kx,ky) such that
Op(planeWave) = μ • planeWave (pointwise).
-/
def PlaneWaveEigen (O : Op2D) : Prop :=
  ∃ μ : ℝ → ℝ → ℂ,
    ∀ (A : ℂ) (kx ky : ℝ),
      O.Op (planeWave A kx ky)
        = (fun x y t => (μ kx ky) * (planeWave A kx ky x y t))

/-- A dispersion-compatibility predicate tying eigenvalues to `omega`. -/
def DispersionCompatible (O : Op2D) : Prop :=
  ∃ μ : ℝ → ℝ → ℂ,
    (∀ (A : ℂ) (kx ky : ℝ),
      O.Op (planeWave A kx ky)
        = (fun x y t => (μ kx ky) * (planeWave A kx ky x y t)))
    ∧ (∀ kx ky : ℝ, μ kx ky = (ToeFormal.CPNLSE2D.omega kx ky : ℂ))

end
end OperatorCore
end ToeFormal
