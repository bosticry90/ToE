/-
ToeFormal/Variational/FirstVariationDeclaredRep32.lean

First-variation representation scaffold on the Rep32 quotient (structural-only).

Scope:
- Uses Field2DRep32 with the Rep32 pairing contract.
- Replays the representation-uniqueness argument without pairing axioms.
- Does not claim any link to FN-01 or Field2D dynamics.
-/

import Mathlib
import ToeFormal.Variational.ActionRep32Def
import ToeFormal.Variational.FirstVariationUniquenessRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

-- Sources (imported): `firstVariationRep32`, `P_rep32`, `RepresentsRep32`, `pairingRep32'`.

/-- Declared EL operator on the Rep32 quotient (structural placeholder). -/
def EL_toe_rep32 : FieldRep32 -> FieldRep32 :=
  actionRep32.EL

/- Derived: the declared EL operator represents the first variation (Rep32 quotient). -/
theorem EL_represents_rep32 : RepresentsRep32 EL_toe_rep32 :=
  actionRep32.represents_EL

/-- Derived identification on the Rep32 quotient. -/
theorem EL_toe_eq_P_rep32 : EL_toe_rep32 = P_rep32 :=
  represents_unique_of_nondegenerate_rep32 pairingRep32_nondegenerate'
    variations_surjective_const_rep32 EL_represents_rep32 P_represents_rep32

end

end Variational
end ToeFormal
