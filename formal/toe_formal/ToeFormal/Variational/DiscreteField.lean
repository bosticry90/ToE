/-
ToeFormal/Variational/DiscreteField.lean

Discrete grid field model (structural-only).
-/

import Mathlib

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Finite grid field: complex values on an nx × ny grid. -/
abbrev FieldGrid (nx ny : Nat) : Type :=
  Fin nx -> Fin ny -> ℂ

end

end Variational
end ToeFormal
