/-
ToeFormal/Constraints/CT01_Target.lean

Historical direct proof of the CT-01 plane-wave target.  The canonical
predicate lives in `CT01_Abstract`; this module retains the direct proof under
a distinct namespace so all tracked modules can coexist in one environment.
No physical claim is added.
-/

import ToeFormal.Constraints.CT01_Abstract

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToeFormal
namespace Constraints
namespace CT01Target

open ToeFormal.CPNLSE2D

/-- Direct recheck: probe admissibility preserves the DR-01 plane-wave target. -/
theorem preserves_DR01_from_admissible
    (P : Constraints.Perturbation)
    (hP : AdmissibleOnPlaneWave P) :
    Constraints.PreservesDR01_onPlaneWaves P := by
  intro A kx ky
  have hPert := EQ02Pert_planeWave_reduces_to_same_coeff_equality P hP A kx ky
  have hUn := EQ02Holds_planeWave_iff A kx ky
  simpa [Constraints.PreservesDR01_onPlaneWaves] using hPert.trans hUn.symm

end CT01Target
end Constraints
end ToeFormal
end
