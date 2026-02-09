/-
ToeFormal/Variational/FirstVariationDeclaredFieldRep.lean

First-variation representation scaffold on the Field2D representation quotient
(structural-only).

Scope:
- Uses Field2DRep with the explicit pairing contract.
- Replays the representation-uniqueness argument without Field2D pairing axioms.
- Does not claim any link to FN-01 or Field2D dynamics.
-/

import Mathlib
import ToeFormal.Variational.ActionRepDefFieldRep
import ToeFormal.Variational.FirstVariationUniquenessFieldRep

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

-- Sources (imported): `firstVariationRep`, `P_rep`, `RepresentsRep`, `pairingRep'`.

/-- Declared EL operator on the representation quotient (structural placeholder). -/
def EL_toe_rep : FieldRep -> FieldRep :=
  actionRep.EL

/- Derived: the declared EL operator represents the first variation (quotient). -/
theorem EL_represents_rep : RepresentsRep EL_toe_rep :=
  actionRep.represents_EL

/-- Derived identification on the representation quotient. -/
theorem EL_toe_eq_P_rep : EL_toe_rep = P_rep :=
  represents_unique_of_nondegenerate_rep pairingRep_nondegenerate'
    variations_surjective_const_rep EL_represents_rep P_represents_rep

end

end Variational
end ToeFormal
