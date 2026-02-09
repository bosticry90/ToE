/-
ToeFormal/Variational/FirstVariationDeclared.lean

First-variation representation scaffold for the declared action.

Scope:
- Structural-only; no analytic derivation.
- Introduces a pairing and a representation predicate for the first variation.
- Derives EL_toe = P_cubic under explicit representation assumptions.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.FieldRepresentation
import ToeFormal.Variational.FirstVariationUniqueness
import ToeFormal.Variational.PairingContract

namespace ToeFormal
namespace Variational

open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false

/-- Pullback pairing nondegeneracy (assumed; injectivity proof pending). -/
constant pairingField2D_nondegenerate :
  ∀ x y : Field, (∀ v : Field, pairingField2D x v = pairingField2D y v) -> x = y

/-- Declared pairing contract (structural-only; pullback via `Rep`). -/
def pairingContract : PairingContract Field :=
  { pairing := pairingField2D
    nondegenerate_second := pairingField2D_nondegenerate }

/-- Pairing induced by the declared contract. -/
def pairing : Field -> Field -> ℝ := pairingContract.pairing

/-- Representation predicate: `E` represents the first variation under `pairing`. -/
def Represents (E : Field -> Field) : Prop :=
  ∀ (δ : Field -> Field) (ψ : Field), firstVariation δ ψ = pairing (E ψ) (δ ψ)

/- Assumption for uniqueness via the declared pairing contract. -/
theorem pairing_nondegenerate : NondegeneratePairing := by
  simpa [pairing] using pairingContract.nondegenerate_second

/- Assumption: the declared EL operator represents the first variation. -/
constant EL_represents : Represents EL_toe

/- Assumption: P_cubic represents the first variation. -/
constant Pcubic_represents : Represents (FN01.P_cubic declared_g)

/-- Derived identification: EL_toe equals the promoted survivor P_cubic. -/
theorem EL_toe_eq_Pcubic : EL_toe = FN01.P_cubic declared_g :=
  represents_unique_of_nondegenerate pairing_nondegenerate variations_surjective_const
    EL_represents Pcubic_represents

end Variational
end ToeFormal
