import Mathlib
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.Constraints.SYM01_PhaseInvariant
import ToeFormal.Constraints.CAUS01_CausalityGate
import ToeFormal.OperatorCore.Op2DMeta

namespace ToeFormal
namespace Constraints
namespace AD01

open ToeFormal.CPNLSE2D

/-
Canonical objects for AD01 gating.

Design:
- `A0` is the canonical global phase action on `Field2D` (pointwise complex phase rotation).
- `G0` is the canonical CAUS-01 gate suite on `Field2D`.
  Currently it enforces at least the "no forcing at zero" condition via `zero`.
-/

abbrev PhaseActionTy : Type :=
  ToeFormal.Constraints.SYM01.PhaseAction Field2D

abbrev CausSuiteTy : Type :=
  ToeFormal.Constraints.CAUS01.CausalityGateSuite Field2D

/-- Canonical SYM-01 phase action: multiply the field by `exp(i θ)` pointwise. -/
noncomputable def A0 : PhaseActionTy where
  act θ ψ :=
    fun x y t => Complex.exp (Complex.I * (θ : ℂ)) * ψ x y t
  act_zero := by
    intro ψ
    funext x y t
    simp
  act_add := by
    intro θ₁ θ₂ ψ
    funext x y t
    -- `exp(i(θ₁+θ₂)) = exp(iθ₁) * exp(iθ₂)` and reassociate
    simp [mul_add, Complex.exp_add, mul_assoc]

/-- Canonical CAUS-01 gate suite: designates the zero field and leaves other tags abstract. -/
noncomputable def G0 : CausSuiteTy where
  zero := fun _x _y _t => (0 : ℂ)
  IsLocal := fun _P => True
  NoEllipticInTime := fun _P => True
  TimeOrderSane := fun _form _P => True
  form := ToeFormal.Constraints.CAUS01.EvolForm.firstOrderTime

-- Canonical NLSE-style commitment at AD01: treat `Op2D` operators on `Field2D` as first-order-time.
instance : ToeFormal.OperatorCore.OpTimeOrder Field2D where
  timeOrder := fun _ => ToeFormal.Constraints.CAUS01.EvolForm.firstOrderTime

end AD01
end Constraints
end ToeFormal
