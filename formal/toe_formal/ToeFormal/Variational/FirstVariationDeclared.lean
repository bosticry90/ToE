/-
ToeFormal/Variational/FirstVariationDeclared.lean

First-variation representation scaffold for the declared action.

Scope:
- Structural-only; no analytic derivation.
- Introduces a pairing and a representation predicate for the first variation.
- Derives EL_toe = P_cubic under explicit representation assumptions.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.FieldRepresentation
import ToeFormal.Variational.FirstVariationRepresentationCore
import ToeFormal.Variational.FirstVariationUniqueness

namespace ToeFormal
namespace Variational

open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false

/--
Derived identification under three explicit retained assumptions: pairing
nondegeneracy and the two first-variation representation hypotheses.
-/
theorem EL_toe_eq_Pcubic
    (hPairing : NondegeneratePairing)
    (hEL : Represents EL_toe)
    (hPcubic : Represents (FN01.P_cubic declared_g)) :
    EL_toe = FN01.P_cubic declared_g :=
  represents_unique_of_nondegenerate hPairing variations_surjective_const hEL hPcubic

end

end Variational
end ToeFormal
