/-
FN-01 — Admissible deformation class (structural Lean layer).

Purpose:
- Provide a typed, purely-structural predicate packaging the minimal gates for a
  candidate deformation/perturbation term `P : Field2D → Field2D`.

This file makes no analytic or physical claims. It is intended as a definition
layer that downstream constraints (e.g. AD-01 / CAUS-01 tightening) can reuse.
-/

import Mathlib
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.Constraints.CT01_Abstract
import ToeFormal.Constraints.SYM01_PhaseInvariant

namespace ToeFormal
namespace Constraints
namespace FN01

open ToeFormal.CPNLSE2D

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Source-free admissibility at the designated zero field: `P 0 = 0`. -/
def NoForcingAt0 (P : Perturbation) : Prop :=
  P 0 = 0

/--
FN-01 candidate deformation class (structural-only):
- no forcing at 0,
- global phase invariance (SYM-01),
- no linear part at 0 (CT-01 abstract criterion).

Note: This is *only* a packaging predicate. Any physical interpretation or
consequence theorems live elsewhere.
-/
def FN01_DeformationClass
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (P : Perturbation) : Prop :=
  NoForcingAt0 P ∧
  SYM01.PhaseInvariant A P ∧
  NoLinearPartAt0_Abstract L P

namespace FN01_DeformationClass

variable {A : SYM01.PhaseAction Field2D}
variable {L : LinearizationAt0_Field2D}
variable {P : Perturbation}

theorem noForcingAt0 (h : FN01_DeformationClass A L P) : NoForcingAt0 P :=
  h.1

theorem phaseInvariant (h : FN01_DeformationClass A L P) : SYM01.PhaseInvariant A P :=
  h.2.1

theorem noLinearPartAt0 (h : FN01_DeformationClass A L P) : NoLinearPartAt0_Abstract L P :=
  h.2.2

end FN01_DeformationClass

/--
FN-01 → DR-01 tightening bridge:

If `P` is admitted by the FN-01 deformation class, then (given a probe-sound
linearization interface specialized to plane waves) `P` preserves DR-01 on the
plane-wave probe family.

This reuses the CT-01 abstract bridge theorem; FN-01 contributes the hypothesis
`NoLinearPartAt0_Abstract` via its packaging predicate.
-/
theorem preserves_DR01_onPlaneWaves_of_deformationClass
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (P : Perturbation)
    (hFN : FN01_DeformationClass A LP.L P) :
    PreservesDR01_onPlaneWaves P := by
  exact
    CT01_noLinearPartAt0_preserves_DR01_onPlaneWaves
      (LP := LP)
      (hProbe := hProbe)
      (P := P)
      (hNL := FN01_DeformationClass.noLinearPartAt0 hFN)

end
end FN01
end Constraints
end ToeFormal
