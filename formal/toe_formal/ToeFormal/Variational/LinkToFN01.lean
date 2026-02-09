/-
ToeFormal/Variational/LinkToFN01.lean

Linkage layer: declared action scaffold -> FN-01 deformation class (structural-only).

Scope:
- Introduces a named relation between the declared EL operator and an FN-01 perturbation.
- Provides routing lemmas from the EL equation to the FN-01 form under explicit assumptions.
- No analytic or physical claims.
-/

import Mathlib
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Constraints.FN01_DeformationClass

namespace ToeFormal
namespace Variational

open ToeFormal.CPNLSE2D
open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false

/--
Relation linking the declared EL operator to an FN-01 perturbation term.
Structural-only; proof obligations are deferred.
-/
def EL_matches_FN01_form (P : Constraints.Perturbation) : Prop :=
  ∀ ψ : Field2D, EL_toe ψ = P ψ

/--
Routing lemma: if the declared EL operator matches an FN-01 perturbation,
then the declared EL equation implies the FN-01 structural form (P ψ = 0).
-/
theorem declared_EL_implies_FN01_form
    (A : Constraints.SYM01.PhaseAction Field2D)
    (L : Constraints.LinearizationAt0_Field2D)
    (P : Constraints.Perturbation)
    (hFN : Constraints.FN01.FN01_DeformationClass A L P)
    (hMatch : EL_matches_FN01_form P)
    (ψ : Field2D) :
    EulerLagrange declaredAction ψ -> P ψ = 0 := by
  intro hEL
  have h0 : EL_toe ψ = 0 := hEL
  have hEq : EL_toe ψ = P ψ := hMatch ψ
  -- Use the FN-01 hypothesis as a declared precondition (structural-only).
  have _hFN : Constraints.FN01.FN01_DeformationClass A L P := hFN
  simpa [hEq] using h0

end Variational
end ToeFormal
