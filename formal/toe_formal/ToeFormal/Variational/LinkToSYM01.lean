/-
ToeFormal/Variational/LinkToSYM01.lean

Linkage layer: Noether scaffold -> SYM-01 phase action + declared evolution (structural-only).

Scope:
- Bridges the SYM-01 phase action interface to the Noether one-parameter action.
- Applies the declared Noether lemma under explicit assumptions.
- Does not claim conservation laws for SYM-01 itself.
-/

import Mathlib
import ToeFormal.Variational.ActionInvariance
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Constraints.SYM01_PhaseInvariant

namespace ToeFormal
namespace Variational

open ToeFormal.CPNLSE2D
open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false

/-- Declared symmetry matches the SYM-01 phase action. -/
def DeclaredSymmetryMatchesSYM01 (A : SYM01.PhaseAction Field2D) : Prop :=
  declaredSymmetry = oneParamAction_of_SYM01 A

/--
Routing lemma: if the declared symmetry matches the SYM-01 phase action and the
declared action is invariant under that action, then the declared Noether
conservation lemma applies.
-/
theorem noether_from_SYM01
    (A : SYM01.PhaseAction Field2D)
    (hMatch : DeclaredSymmetryMatchesSYM01 A)
    (hInv : ActionInvariant declaredAction (oneParamAction_of_SYM01 A)) :
    Conserved declaredEvolution declaredQuantity := by
  have hInv' : ActionInvariant declaredAction declaredSymmetry := by
    simpa [hMatch] using hInv
  exact declared_noether_conservation hInv'

end Variational
end ToeFormal
