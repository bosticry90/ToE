/-
This proof variant was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
Project request UUID: f43cd06c-7ee1-4e7a-bf25-8416190fb1d1

The original repeated every declaration in `CT01_Target` and therefore could
not be co-imported with it.  This integrated form preserves the Aristotle
provenance and proof witness while reusing the canonical target theorem.
-/

import ToeFormal.Constraints.CT01_Target

namespace ToeFormal
namespace Constraints
namespace CT01TargetAristotle

open ToeFormal.CPNLSE2D

/-- Aristotle-path recheck of the nonpromotional CT-01 target. -/
theorem preserves_DR01_from_admissible_recheck
    (P : Constraints.Perturbation)
    (hP : AdmissibleOnPlaneWave P) :
    Constraints.PreservesDR01_onPlaneWaves P := by
  exact CT01Target.preserves_DR01_from_admissible P hP

end CT01TargetAristotle
end Constraints
end ToeFormal
