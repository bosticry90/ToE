/-
FN-01 — CAUS-01 core bridge (Lean-first).

Purpose:
- Demonstrate FN-01 can depend on the CAUS-01 *core* surface structurally.
- Keep this module decoupled from the CAUS-01 gate-suite.

This file intentionally imports:
- CAUS01_CausalityCore (the minimal TimeOrder/Admissible surface)
- FN01_DeformationClass (FN packaging predicate)

No gate-suite imports live here.
-/

import ToeFormal.Constraints.CAUS01_CausalityCore
import ToeFormal.Constraints.FN01_DeformationClass

namespace ToeFormal
namespace Constraints
namespace FN01

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev TimeOrder := CAUS01.TimeOrder
abbrev Admissible := CAUS01.Admissible

/-- Bridge re-export: admissibility is reflexive (inherited from the preorder). -/
theorem caus01_admissible_refl
    (T : TimeOrder) (t : T.Time) :
    Admissible T t t := by
  simpa using (CAUS01.CAUS01_admissible_refl T t)

/-- Bridge re-export: admissibility composes transitively (inherited from the preorder). -/
theorem caus01_admissible_trans
    (T : TimeOrder) {a b c : T.Time} :
    Admissible T a b → Admissible T b c → Admissible T a c := by
  intro hab hbc
  exact CAUS01.CAUS01_admissible_trans T hab hbc

/-- Bridge re-export: no backward admissibility under strict order. -/
theorem caus01_no_backward
    (T : TimeOrder) {t₁ t₂ : T.Time} (h : t₂ < t₁) :
    ¬ Admissible T t₁ t₂ := by
  simpa using (CAUS01.CAUS01_no_backward (T := T) h)

end
end FN01
end Constraints
end ToeFormal
