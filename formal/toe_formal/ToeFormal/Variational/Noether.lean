/-
ToeFormal/Variational/Noether.lean

Phase 3 (Noether invariants) - abstract scaffold.

Scope:
- Structural-only; no analytic derivations.
- Defines a one-parameter symmetry action and an evolution flow.
- Defines action-invariance and conservation along a flow.
- Provides a Noether-style lemma under explicit assumptions.
-/

import Mathlib
import ToeFormal.Variational.ActionScaffold

namespace ToeFormal
namespace Variational

universe u

noncomputable section
set_option autoImplicit false

/-- One-parameter action on a field type (additive parameter). -/
structure OneParameterAction (F : Type u) where
  act : ℝ → F → F
  act_zero : ∀ ψ : F, act 0 ψ = ψ
  act_add : ∀ (t₁ t₂ : ℝ) (ψ : F), act (t₁ + t₂) ψ = act t₁ (act t₂ ψ)

attribute [simp] OneParameterAction.act_zero OneParameterAction.act_add

/-- One-parameter evolution flow (additive time parameter). -/
structure Evolution (F : Type u) where
  flow : ℝ → F → F
  flow_zero : ∀ ψ : F, flow 0 ψ = ψ
  flow_add : ∀ (t₁ t₂ : ℝ) (ψ : F), flow (t₁ + t₂) ψ = flow t₁ (flow t₂ ψ)

attribute [simp] Evolution.flow_zero Evolution.flow_add

/-- Action invariance under a symmetry action. -/
def ActionInvariant {F : Type u} (A : ActionScaffold F) (G : OneParameterAction F) : Prop :=
  ∀ (t : ℝ) (ψ : F), action A (G.act t ψ) = action A ψ

/-- Conservation of a quantity along an evolution flow. -/
def Conserved {F : Type u} (E : Evolution F) (Q : F → ℝ) : Prop :=
  ∀ (t : ℝ) (ψ : F), Q (E.flow t ψ) = Q ψ

/--
Assumptions capturing the Noether bridge:
if the action is invariant under a symmetry, then the quantity is conserved.
-/
structure NoetherAssumptions (F : Type u)
    (A : ActionScaffold F) (G : OneParameterAction F) (E : Evolution F) (Q : F → ℝ) : Prop where
  noether : ActionInvariant A G → Conserved E Q

/-- Abstract Noether lemma (structural-only). -/
theorem noether_conservation
    {F : Type u} (A : ActionScaffold F) (G : OneParameterAction F)
    (E : Evolution F) (Q : F → ℝ)
    (h : NoetherAssumptions F A G E Q) :
    ActionInvariant A G → Conserved E Q := by
  intro hInv
  exact h.noether hInv

end
end Variational
end ToeFormal
