/-
FN-01 — CAUS-01 core consumer (Lean-first).

Purpose:
- Confirm CAUS-01's minimal core surface is reusable from the FN layer.
- Provide FN-01-local theorem names that re-export the CAUS-01 core facts.

This file intentionally imports only CAUS01_CausalityCore.
-/

import ToeFormal.Constraints.CAUS01_CausalityCore

namespace ToeFormal
namespace Constraints
namespace FN01

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
Thin consumer: imports ONLY CAUS core surface and re-exports the stable lemma API.
-/

abbrev TimeOrder := CAUS01.TimeOrder
abbrev Admissible := CAUS01.Admissible

/-- FN-01-facing re-export: admissibility is reflexive. -/
theorem caus01_admissible_refl
    (T : TimeOrder) (t : T.Time) :
    Admissible T t t := by
  simpa using (CAUS01.CAUS01_admissible_refl T t)

/-- FN-01-facing re-export: admissibility composes transitively. -/
theorem caus01_admissible_trans
    (T : TimeOrder) {a b c : T.Time} :
    Admissible T a b → Admissible T b c → Admissible T a c := by
  intro hab hbc
  exact CAUS01.CAUS01_admissible_trans T hab hbc

/-- FN-01-facing re-export: no backward admissibility under strict order. -/
theorem caus01_no_backward
    (T : TimeOrder) {t₁ t₂ : T.Time} (h : t₂ < t₁) :
    ¬ Admissible T t₁ t₂ := by
  simpa using (CAUS01.CAUS01_no_backward (T := T) h)

end
end FN01
end Constraints
end ToeFormal
