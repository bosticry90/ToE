/-
ToeFormal/Variational/FirstVariationUniquenessFieldRep.lean

Representation-quotient uniqueness for first-variation representation via the
pairing contract on Field2DRep.

Scope:
- Structural-only; no analytic content.
- Uses the Field2DRep pairing contract and constant-variation surjectivity.
- Avoids any Field2D pairing assumptions.
-/

import Mathlib
import ToeFormal.Variational.FirstVariationRepDefFieldRep

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

-- Sources (imported): `firstVariationRep`, `RepresentsRep`,
-- `pairingRep'`, `pairingContractFieldRep`.

/-- Variations can reach any value at a fixed field point (representation quotient). -/
def VariationsSurjectiveRep : Prop :=
  ∀ (ψ : FieldRep) (v : FieldRep), ∃ δ : FieldRep -> FieldRep, δ ψ = v

/-- Variations are surjective via constant variations (representation quotient). -/
theorem variations_surjective_const_rep : VariationsSurjectiveRep := by
  intro ψ v
  refine ⟨fun _ => v, rfl⟩

/-- Pairing is nondegenerate in the second slot (representation quotient). -/
def NondegeneratePairingRep : Prop :=
  ∀ (x y : FieldRep), (∀ v : FieldRep, pairingRep' x v = pairingRep' y v) -> x = y

/-- Nondegeneracy derived from the representation-quotient pairing contract. -/
theorem pairingRep_nondegenerate' : NondegeneratePairingRep := by
  simpa [pairingRep'] using pairingContractFieldRep.nondegenerate_second

/-- Uniqueness of representation (representation quotient). -/
theorem represents_unique_of_nondegenerate_rep
    (hnd : NondegeneratePairingRep)
    (hsurj : VariationsSurjectiveRep)
    {E1 E2 : FieldRep -> FieldRep}
    (h1 : RepresentsRep E1)
    (h2 : RepresentsRep E2) :
    E1 = E2 := by
  funext ψ
  apply hnd
  intro v
  obtain ⟨δ, hδ⟩ := hsurj ψ v
  have h1' := h1 δ ψ
  have h2' := h2 δ ψ
  calc
    pairingRep' (E1 ψ) v = pairingRep' (E1 ψ) (δ ψ) := by simp [hδ]
    _ = firstVariationRep δ ψ := by symm; exact h1'
    _ = pairingRep' (E2 ψ) (δ ψ) := by exact h2'
    _ = pairingRep' (E2 ψ) v := by simp [hδ]

end

end Variational
end ToeFormal
