/-
AD-01 — CAUS-01 core consumer (Lean-first).

Purpose:
- Demonstrate that the minimal CAUS-01 core surface is usable downstream.
- Provide AD-01-local lemma names that re-export the CAUS-01 core facts.

This file intentionally imports only CAUS01_CausalityCore.
-/

import ToeFormal.Constraints.CAUS01_CausalityCore

namespace ToeFormal
namespace Constraints
namespace AD01

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- AD-01-facing re-export: admissibility is reflexive. -/
theorem caus01_admissible_refl
    (T : CAUS01.TimeOrder) (t : T.Time) :
    CAUS01.Admissible T t t := by
  simpa using (CAUS01.CAUS01_admissible_refl T t)

/-- AD-01-facing re-export: admissibility composes transitively. -/
theorem caus01_admissible_trans
    (T : CAUS01.TimeOrder) {a b c : T.Time} :
    CAUS01.Admissible T a b → CAUS01.Admissible T b c → CAUS01.Admissible T a c := by
  intro hab hbc
  exact CAUS01.CAUS01_admissible_trans T hab hbc

/-- AD-01-facing re-export: no backward admissibility under strict order. -/
theorem caus01_no_backward
    (T : CAUS01.TimeOrder) {t₁ t₂ : T.Time} (h : t₂ < t₁) :
    ¬ CAUS01.Admissible T t₁ t₂ := by
  simpa using (CAUS01.CAUS01_no_backward (T := T) h)

end
end AD01
end Constraints
end ToeFormal
