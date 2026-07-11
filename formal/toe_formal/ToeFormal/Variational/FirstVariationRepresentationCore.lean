/-
ToeFormal/Variational/FirstVariationRepresentationCore.lean

Axiom-free shared definitions for first-variation representation.

Scope:
- Defines the declared pullback pairing and representation predicate.
- Breaks the former import cycle between `FirstVariationDeclared` and
  `FirstVariationUniqueness` while keeping the shared definitions axiom-free.
- Contains no analytic derivation and earns no scientific promotion.
- Keeps all explicit assumptions in their existing declaring modules.
-/

import Mathlib
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.FieldRepresentation

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Pullback pairing used by the declared first-variation scaffold. -/
def pairing : Field -> Field -> ℝ := pairingField2D

/-- Representation predicate: `E` represents the first variation under `pairing`. -/
def Represents (E : Field -> Field) : Prop :=
  ∀ (δ : Field -> Field) (ψ : Field), firstVariation δ ψ = pairing (E ψ) (δ ψ)

end

end Variational
end ToeFormal
