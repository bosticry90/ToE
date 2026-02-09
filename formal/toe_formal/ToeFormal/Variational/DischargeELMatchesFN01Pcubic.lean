/-
ToeFormal/Variational/DischargeELMatchesFN01Pcubic.lean

Discharge: EL_matches_FN01_form for the promoted FN-01 survivor P_cubic.

Scope:
- Structural-only; EL operator matches P_cubic under first-variation representation assumptions.
- Uses the FN-01 Candidate API import surface.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.FirstVariationDeclared
import ToeFormal.Variational.LinkToFN01

namespace ToeFormal
namespace Variational

open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false

/-- Declared EL operator matches the promoted FN-01 candidate P_cubic. -/
theorem EL_matches_Pcubic : EL_matches_FN01_form (FN01.P_cubic declared_g) := by
  intro ψ
  -- Derived from the first-variation representation assumptions.
  simpa [EL_toe_eq_Pcubic] 

/--
Routing lemma specialized to P_cubic: if P_cubic is admitted by FN-01,
then the declared EL equation implies P_cubic ψ = 0.
-/
theorem declared_EL_implies_Pcubic
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (hFN : FN01.FN01_DeformationClass A L (FN01.P_cubic declared_g))
    (ψ : Field2D) :
    EulerLagrange declaredAction ψ -> (FN01.P_cubic declared_g) ψ = 0 := by
  exact
    declared_EL_implies_FN01_form
      (A := A)
      (L := L)
      (P := FN01.P_cubic declared_g)
      (hFN := hFN)
      (hMatch := EL_matches_Pcubic)
      (ψ := ψ)

end Variational
end ToeFormal
