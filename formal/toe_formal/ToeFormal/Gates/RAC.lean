/-
Regularity Admissibility Condition (RAC) hooks.

Documentation-level classifiers only; no proofs or axioms.
-/

namespace ToeFormal.Gates

/-- Energy-regime classifier for RAC (documentation hook only). -/
inductive RAC_EnergyClass where
  | conservative
  | dissipative
  deriving DecidableEq, Repr

end ToeFormal.Gates
