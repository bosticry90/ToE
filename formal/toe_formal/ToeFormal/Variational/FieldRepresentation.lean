/-
ToeFormal/Variational/FieldRepresentation.lean

Field2D → finite-grid representation (structural-only).

Scope:
- Pins a concrete grid size for the COMP-FN-REP scaffold.
- Declares a representation map `Rep`.
- Defines the pullback pairing on Field2D via `gridPairing`.
- Records the explicit quotient/equality policy (identify by `Rep`).
- No injectivity proof yet; this is a design stub.
-/

import Mathlib
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.Variational.DiscreteField
import ToeFormal.Variational.PairingConcreteGrid

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Local alias for the project field type. -/
abbrev Field2D : Type := ToeFormal.CPNLSE2D.Field2D

/-- Pinned representation grid size (audited; update State_of_the_Theory.md if changed). -/
def repNx : Nat := 32

/-- Pinned representation grid size (audited; update State_of_the_Theory.md if changed). -/
def repNy : Nat := 32

/-- Shorthand for the pinned grid type. -/
abbrev RepGrid : Type := FieldGrid repNx repNy

/-- Representation map from Field2D to the pinned grid (design stub). -/
axiom Rep : Field2D -> RepGrid

/-- Pullback pairing on Field2D induced by the grid pairing via `Rep`. -/
def pairingField2D (x v : Field2D) : ℝ :=
  gridPairing (Rep x) (Rep v)

/-- Equality policy: identify fields with the same representation. -/
def RepEq (x y : Field2D) : Prop := Rep x = Rep y

/-- Setoid for the representation quotient (policy choice for nondegeneracy). -/
def RepSetoid : Setoid Field2D :=
  { r := RepEq
    iseqv := by
      refine ⟨?refl, ?symm, ?trans⟩
      · intro x
        rfl
      · intro x y h
        simpa [RepEq] using h.symm
      · intro x y z hxy hyz
        simpa [RepEq] using hxy.trans hyz }

/-- Representation quotient type for the chosen equality policy. -/
abbrev Field2DRep : Type := Quot RepSetoid

/-- Representation map on the quotient (well-defined by construction). -/
def RepQ : Field2DRep -> RepGrid :=
  Quot.lift Rep (by
    intro x y h
    simpa [RepEq] using h)

/-- Pullback pairing on the quotient type. -/
def pairingRep (x v : Field2DRep) : ℝ :=
  gridPairing (RepQ x) (RepQ v)

end

end Variational
end ToeFormal
