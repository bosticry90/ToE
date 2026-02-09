/-
ToeFormal/Variational/FirstVariationUniquenessRep32.lean

Rep32 uniqueness for first-variation representation via the Rep32 pairing contract.

Scope:
- Structural-only; no analytic content.
- Uses the Rep32 quotient pairing contract and constant-variation surjectivity.
- Avoids any Field2D pairing assumptions.
-/

import Mathlib
import ToeFormal.Variational.FirstVariationRep32Def

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

-- Sources (imported): `firstVariationRep32`, `RepresentsRep32`,
-- `pairingRep32'`, `pairingContractRep`.

/-- Variations can reach any value at a fixed field point (Rep32 quotient). -/
def VariationsSurjectiveRep32 : Prop :=
  ∀ (ψ : FieldRep32) (v : FieldRep32), ∃ δ : FieldRep32 -> FieldRep32, δ ψ = v

/-- Variations are surjective via constant variations (Rep32 quotient). -/
theorem variations_surjective_const_rep32 : VariationsSurjectiveRep32 := by
  intro ψ v
  refine ⟨fun _ => v, rfl⟩

/-- Pairing is nondegenerate in the second slot (Rep32 quotient). -/
def NondegeneratePairingRep32 : Prop :=
  ∀ (x y : FieldRep32), (∀ v : FieldRep32, pairingRep32' x v = pairingRep32' y v) -> x = y

/-- Nondegeneracy derived from the Rep32 pairing contract. -/
theorem pairingRep32_nondegenerate' : NondegeneratePairingRep32 := by
  simpa [pairingRep32'] using pairingContractRep.nondegenerate_second

/-- Uniqueness of representation (Rep32 quotient). -/
theorem represents_unique_of_nondegenerate_rep32
    (hnd : NondegeneratePairingRep32)
    (hsurj : VariationsSurjectiveRep32)
    {E1 E2 : FieldRep32 -> FieldRep32}
    (h1 : RepresentsRep32 E1)
    (h2 : RepresentsRep32 E2) :
    E1 = E2 := by
  funext ψ
  apply hnd
  intro v
  obtain ⟨δ, hδ⟩ := hsurj ψ v
  have h1' := h1 δ ψ
  have h2' := h2 δ ψ
  calc
    pairingRep32' (E1 ψ) v = pairingRep32' (E1 ψ) (δ ψ) := by simp [hδ]
    _ = firstVariationRep32 δ ψ := by symm; exact h1'
    _ = pairingRep32' (E2 ψ) (δ ψ) := by exact h2'
    _ = pairingRep32' (E2 ψ) v := by simp [hδ]

end

end Variational
end ToeFormal
