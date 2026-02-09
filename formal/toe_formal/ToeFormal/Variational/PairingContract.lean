/-
ToeFormal/Variational/PairingContract.lean

Pairing contract for first-variation representation (structural-only).

Scope:
- Packages a pairing with a nondegeneracy-in-the-second-slot contract.
- Keeps assumptions explicit and replaceable.
-/

import Mathlib

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Pairing contract: pairing plus nondegeneracy in the second slot. -/
structure PairingContract (F : Type) where
  pairing : F -> F -> ℝ
  nondegenerate_second : ∀ x y : F, (∀ v : F, pairing x v = pairing y v) -> x = y

end

end Variational
end ToeFormal
