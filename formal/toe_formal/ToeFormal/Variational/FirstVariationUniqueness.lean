/-
ToeFormal/Variational/FirstVariationUniqueness.lean

Structural uniqueness for first-variation representation via nondegenerate pairing.

Scope:
- Structural-only; no analytic content.
- Replaces a raw uniqueness axiom with explicit nondegeneracy + surjectivity assumptions.
-/

import Mathlib
import ToeFormal.Variational.FirstVariationDeclared

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Variations can reach any value at a fixed field point. -/
def VariationsSurjective : Prop :=
  ∀ (ψ : Field) (v : Field), ∃ δ : Field -> Field, δ ψ = v

/-- Variations are surjective via constant variations (structural-only). -/
theorem variations_surjective_const : VariationsSurjective := by
  intro ψ v
  refine ⟨fun _ => v, rfl⟩

/-- Pairing is nondegenerate in the second slot. -/
def NondegeneratePairing : Prop :=
  ∀ (x y : Field), (∀ v : Field, pairing x v = pairing y v) -> x = y

/-- Uniqueness of representation derived from nondegeneracy + variation surjectivity. -/
theorem represents_unique_of_nondegenerate
    (hnd : NondegeneratePairing)
    (hsurj : VariationsSurjective)
    {E1 E2 : Field -> Field}
    (h1 : Represents E1)
    (h2 : Represents E2) :
    E1 = E2 := by
  funext ψ
  apply hnd
  intro v
  obtain ⟨δ, hδ⟩ := hsurj ψ v
  have h1' := h1 δ ψ
  have h2' := h2 δ ψ
  calc
    pairing (E1 ψ) v = pairing (E1 ψ) (δ ψ) := by simpa [hδ]
    _ = firstVariation δ ψ := by symm; exact h1'
    _ = pairing (E2 ψ) (δ ψ) := by exact h2'
    _ = pairing (E2 ψ) v := by simpa [hδ]

end Variational
end ToeFormal
