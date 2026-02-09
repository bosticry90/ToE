import Mathlib
import ToeFormal.OperatorCore.OperatorSignature
import ToeFormal.Constraints.SYM01_PhaseInvariant
import ToeFormal.Constraints.CAUS01_CausalityGate

namespace ToeFormal
namespace Constraints

open ToeFormal.OperatorCore

/-
AD01 — Step 1 (Lean-first, Path 1): canonical admissibility predicate surface.

Goal:
- Define one structural predicate `AdmissibleOp` for operator candidates.
- It is the conjunction of:
    (a) dispersion compatibility (DR-01 semantics)  [via OperatorCore.DispersionCompatible]
    (b) symmetry gate compliance (SYM-01 semantics) [abstracted as a tag]
    (c) causality/admissibility compliance (CAUS-01 semantics) [abstracted as a tag]

Non-goals:
- No breakage lemma here.
- No physics claims.
- No attempt to derive gates from analysis.
-/

/-- SYM-01 compliance tag for operators (semantic; caller supplies meaning). -/
class SymmGate (α : Type) where
  symmOk : α → Prop

/-- CAUS-01 compliance tag for operators (semantic; caller supplies meaning). -/
class CausGate (α : Type) where
  causOk : α → Prop

/--
AD01 admissibility predicate.

NOTE:
- This file assumes `ToeFormal.OperatorCore.DispersionCompatible : α → Prop` is available
  from `ToeFormal.OperatorCore.OperatorSignature`.
- If your `DispersionCompatible` has additional parameters (e.g., probe family), adapt ONLY
  this definition’s arguments, not the surrounding structure.
-/
def AdmissibleOp (α : Type) [SymmGate α] [CausGate α]
    (DispersionCompatible : α → Prop) (O : α) : Prop :=
  DispersionCompatible O ∧ SymmGate.symmOk O ∧ CausGate.causOk O

theorem admissibleOp_dispersion (α : Type) [SymmGate α] [CausGate α]
    (DispersionCompatible : α → Prop) (O : α) :
    AdmissibleOp α DispersionCompatible O → DispersionCompatible O := by
  intro h; exact h.left

theorem admissibleOp_symm (α : Type) [SymmGate α] [CausGate α]
    (DispersionCompatible : α → Prop) (O : α) :
    AdmissibleOp α DispersionCompatible O → SymmGate.symmOk O := by
  intro h; exact h.right.left

theorem admissibleOp_caus (α : Type) [SymmGate α] [CausGate α]
    (DispersionCompatible : α → Prop) (O : α) :
    AdmissibleOp α DispersionCompatible O → CausGate.causOk O := by
  intro h; exact h.right.right

end Constraints
end ToeFormal
