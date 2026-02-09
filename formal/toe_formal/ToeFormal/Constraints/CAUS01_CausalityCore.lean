/-
CAUS-01 — Causality core (Lean-first tightening).

Purpose:
- Provide a minimal, reusable definition surface for time ordering and
  an admissibility relation derived from that order.

This file is intentionally structural:
- no PDE claims
- no physical interpretation
- admissibility is defined purely in terms of the time preorder
-/

import Mathlib

namespace ToeFormal
namespace Constraints
namespace CAUS01

universe u

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/--
A minimal packaging of a time domain together with a preorder.

Downstream modules can depend on this without introducing any separate
"causality notion" beyond the order itself.
-/
structure TimeOrder where
  Time : Type u
  instPreorder : Preorder Time

attribute [instance] TimeOrder.instPreorder

/-- Causal admissibility derived from the preorder: `t₁` is admissible before `t₂` iff `t₁ ≤ t₂`. -/
def Admissible (T : TimeOrder) (t₁ t₂ : T.Time) : Prop :=
  t₁ ≤ t₂

/-- Reflexivity of admissibility (inherited from `Preorder`). -/
theorem CAUS01_admissible_refl (T : TimeOrder) (t : T.Time) :
    Admissible T t t := by
  simp [Admissible]

/-- Transitivity of admissibility (inherited from `Preorder`). -/
theorem CAUS01_admissible_trans (T : TimeOrder) {a b c : T.Time} :
    Admissible T a b → Admissible T b c → Admissible T a c := by
  intro hab hbc
  exact le_trans hab hbc

/-- No backward admissibility: if `t₂ < t₁` then `¬ Admissible t₁ t₂`. -/
theorem CAUS01_no_backward (T : TimeOrder) {t₁ t₂ : T.Time} (h : t₂ < t₁) :
    ¬ Admissible T t₁ t₂ := by
  -- `not_le_of_gt : b < a → ¬ a ≤ b`
  simpa [Admissible] using (not_le_of_gt h)

end
end CAUS01
end Constraints
end ToeFormal
