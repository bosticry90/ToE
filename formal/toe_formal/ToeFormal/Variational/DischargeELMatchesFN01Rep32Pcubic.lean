/-
ToeFormal/Variational/DischargeELMatchesFN01Rep32Pcubic.lean

Rep32-lane discharge: pin the comparison operator to a Rep32 analogue of P_cubic.

Scope:
- Structural-only; does not assert any FN-01 import on Field2DRep32.
- Fixes a concrete candidate operator `P_cubic_rep32`.
- Derives EL_toe_rep32 = P_cubic_rep32 declared_g_rep32 from the Rep32 uniqueness scaffold.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.FirstVariationDeclaredRep32
import ToeFormal.Variational.ActionRep32QuadraticCubic

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Rep32 analogue of the cubic coupling parameter (default binding alias). -/
abbrev declared_g_rep32 : ℂ := declared_g_rep32_default

/-- Rep32 analogue of the cubic FN-01 candidate (definition). -/
def P_cubic_rep32 : ℂ -> Field2DRep32 -> Field2DRep32 :=
  P_cubic_rep32_def

/-- Pin the abstract comparison operator to the Rep32 cubic candidate (theorem route). -/
theorem P_rep32_def : P_rep32 = P_cubic_rep32 declared_g_rep32 := by
  funext ψ
  refine Quot.inductionOn ψ ?_
  intro x
  rfl

/-- Explicit identification route under a supplied Rep32-to-cubic equality. -/
theorem EL_toe_eq_Pcubic_rep32_of_hP
    (hP : P_rep32 = P_cubic_rep32 declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32 declared_g_rep32 := by
  simpa [hP] using EL_toe_eq_P_rep32

/-- Derived identification: EL_toe_rep32 equals the Rep32 cubic candidate. -/
theorem EL_toe_eq_Pcubic_rep32 : EL_toe_rep32 = P_cubic_rep32 declared_g_rep32 := by
  exact EL_toe_eq_Pcubic_rep32_of_hP P_rep32_def

end

end Variational
end ToeFormal
