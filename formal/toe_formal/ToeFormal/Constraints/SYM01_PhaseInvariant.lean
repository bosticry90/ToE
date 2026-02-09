/-
SYM-01 (Gate S1) — Minimal Lean interface for global phase invariance.

Purpose:
- Provide a purely structural (non-analytic) interface for “global phase action” on a field type `F`
  and a predicate stating that a deformation `P : F → F` is phase invariant:
    P(phase θ ψ) = phase θ (P ψ)

This file makes NO physical claims and imports no PDE/Noether machinery.
-/

import Mathlib

namespace ToeFormal
namespace Constraints
namespace SYM01

universe u

/-- Abstract global-phase action on a field type `F`. -/
structure PhaseAction (F : Type u) where
  /-- Apply a global phase parameter `θ : ℝ` to a field `ψ : F`. -/
  act : ℝ → F → F
  /-- Identity phase acts as identity. -/
  act_zero : ∀ ψ : F, act 0 ψ = ψ
  /-- Additive composition of phases. -/
  act_add : ∀ (θ₁ θ₂ : ℝ) (ψ : F), act (θ₁ + θ₂) ψ = act θ₁ (act θ₂ ψ)

attribute [simp] PhaseAction.act_zero PhaseAction.act_add

variable {F : Type u}

/--
Gate S1 (Global phase invariance), purely structural:

`P` is phase-invariant (equivariant under the global phase action `A`) iff
for all `θ` and `ψ`: `P (A.act θ ψ) = A.act θ (P ψ)`.
-/
def PhaseInvariant (A : PhaseAction F) (P : F → F) : Prop :=
  ∀ (θ : ℝ) (ψ : F), P (A.act θ ψ) = A.act θ (P ψ)

namespace PhaseInvariant

variable (A : PhaseAction F)

/-- The identity map is phase-invariant. -/
theorem id : PhaseInvariant A (fun ψ : F => ψ) := by
  intro θ ψ
  rfl

/-- If `P` and `Q` are phase-invariant, then their composition is phase-invariant. -/
theorem comp {P Q : F → F}
    (hP : PhaseInvariant A P) (hQ : PhaseInvariant A Q) :
    PhaseInvariant A (fun ψ => P (Q ψ)) := by
  intro θ ψ
  calc
    P (Q (A.act θ ψ)) = P (A.act θ (Q ψ)) := by
      simpa [PhaseInvariant] using congrArg P (hQ θ ψ)
    _ = A.act θ (P (Q ψ)) := by
      simpa [PhaseInvariant] using hP θ (Q ψ)

end PhaseInvariant

/-
Optional: If later you choose to model the phase action concretely via Complex scaling,
you can instantiate `PhaseAction` for your `Field2D` type elsewhere, without changing
this interface.
-/

end SYM01
end Constraints
end ToeFormal
