/-
ToeFormal/Variational/FieldRepresentationRep32.lean

Concrete representation lane using pinned sample evaluation (Rep32).

Scope:
- Defines `Rep32` by evaluation on the pinned sample points.
- Defines the quotient policy for Rep32 (RepEq32 / Field2DRep32).
- Provides delta-coverage witnesses without axioms.
- Keeps the abstract `Rep` lane separate.
-/

import Mathlib
import ToeFormal.Variational.FieldRepresentationSample

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Concrete representation by sampling on the pinned grid. -/
def Rep32 (ψ : Field2D) : RepGrid :=
  fun i j => ψ (sampleX i) (sampleY j) sampleT

/-- Equality policy induced by Rep32. -/
def RepEq32 (x y : Field2D) : Prop := Rep32 x = Rep32 y

/-- Setoid for the Rep32 quotient. -/
def RepSetoid32 : Setoid Field2D :=
  { r := RepEq32
    iseqv := by
      refine ⟨?refl, ?symm, ?trans⟩
      · intro x
        rfl
      · intro x y h
        simpa [RepEq32] using h.symm
      · intro x y z hxy hyz
        simpa [RepEq32] using hxy.trans hyz }

/-- Quotient type for the Rep32 policy. -/
abbrev Field2DRep32 : Type := Quot RepSetoid32

/-- Representation map on the quotient. -/
def RepQ32 : Field2DRep32 -> RepGrid :=
  Quot.lift Rep32 (by
    intro x y h
    simpa [RepEq32] using h)

/-- Pullback pairing on the Rep32 quotient. -/
def pairingRep32 (x v : Field2DRep32) : ℝ :=
  gridPairing (RepQ32 x) (RepQ32 v)

/-- Rep32 agrees with RepSample on embedded samples. -/
theorem Rep32_on_samples (s : Field2DSample) :
    Rep32 (toField2D s) = RepSample s := by
  rfl

/-- Delta coverage for Rep32 (value `1`). -/
theorem Rep32_hits_delta_one :
    ∀ (i : Fin repNx) (j : Fin repNy), ∃ ψ : Field2D, Rep32 ψ = delta i j 1 := by
  intro i j
  refine ⟨toField2D ⟨delta i j 1⟩, ?_⟩
  calc
    Rep32 (toField2D ⟨delta i j 1⟩)
        = RepSample ⟨delta i j 1⟩ := Rep32_on_samples _
    _ = delta i j 1 := by
        simp [RepSample_eq_grid]

/-- Delta coverage for Rep32 (value `I`). -/
theorem Rep32_hits_delta_I :
    ∀ (i : Fin repNx) (j : Fin repNy), ∃ ψ : Field2D, Rep32 ψ = delta i j Complex.I := by
  intro i j
  refine ⟨toField2D ⟨delta i j Complex.I⟩, ?_⟩
  calc
    Rep32 (toField2D ⟨delta i j Complex.I⟩)
        = RepSample ⟨delta i j Complex.I⟩ := Rep32_on_samples _
    _ = delta i j Complex.I := by
        simp [RepSample_eq_grid]

end

end Variational
end ToeFormal
