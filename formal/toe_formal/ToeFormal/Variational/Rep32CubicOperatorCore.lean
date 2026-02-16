/-
ToeFormal/Variational/Rep32CubicOperatorCore.lean

Rep32 cubic-operator core (constructive default binding surface).

Scope:
- Defines a Rep32 cubic operator independently of GR01 bridge/plumbing modules.
- Provides a pinned default coupling constant for v0 default binding.
- No action/variation claims are made in this module.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentationRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Pointwise cubic operator on `Field2D` (core surface). -/
def cubicField2D_core (g : ℂ) (ψ : Field2D) : Field2D :=
  fun x y t => g * ((Complex.normSq (ψ x y t)) : ℂ) * (ψ x y t)

/-- Core Rep32 lift of the pointwise cubic operator. -/
def P_cubic_rep32_core (g : ℂ) : Field2DRep32 -> Field2DRep32 :=
  Quot.lift (fun ψ => Quot.mk _ (cubicField2D_core g ψ))
    (by
      intro x y h
      apply Quot.sound
      funext i j
      have hxy := congrArg (fun f => f i j) h
      simp [Rep32] at hxy
      simp [cubicField2D_core, Rep32, hxy])

/-- Pinned default coupling for the v0 Rep32 default-binding route. -/
def declared_g_rep32_default : ℂ := 1

end

end Variational
end ToeFormal
