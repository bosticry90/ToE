/-
FN-01 — CAUS-01 core bridge (Lean-first).

This bridge retains the dependency demonstration between the FN packaging
surface and the minimal CAUS-01 consumer API.  The original file duplicated
all declarations from `FN01_CausalityCoreConsumer`, preventing both tracked
modules from being imported together.  No gate-suite or physical claim is
introduced here.
-/

import ToeFormal.Constraints.FN01_CausalityCoreConsumer
import ToeFormal.Constraints.FN01_DeformationClass

namespace ToeFormal
namespace Constraints
namespace FN01
namespace CausalityCoreBridge

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Bridge witness: the thin FN consumer's reflexivity fact remains available. -/
theorem admissible_refl_recheck
    (T : FN01.TimeOrder) (t : T.Time) :
    FN01.Admissible T t t := by
  exact FN01.caus01_admissible_refl T t

/-- Bridge witness: the thin FN consumer's transitivity fact remains available. -/
theorem admissible_trans_recheck
    (T : FN01.TimeOrder) {a b c : T.Time} :
    FN01.Admissible T a b → FN01.Admissible T b c → FN01.Admissible T a c := by
  exact FN01.caus01_admissible_trans T

/-- Bridge witness: the thin FN consumer's no-backward fact remains available. -/
theorem no_backward_recheck
    (T : FN01.TimeOrder) {t₁ t₂ : T.Time} (h : t₂ < t₁) :
    ¬ FN01.Admissible T t₁ t₂ := by
  exact FN01.caus01_no_backward T h

end

end CausalityCoreBridge
end FN01
end Constraints
end ToeFormal
