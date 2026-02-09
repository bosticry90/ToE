/-
CT-01g — CP-NLSE instance-layer shim.

Purpose:
- Provide a stable downstream theorem name by re-exporting the CT-01 abstract bridge
  theorem specialized to the canonical plane-wave probe family.

No new analytic assumptions are introduced here.
-/

import Mathlib
import ToeFormal.Constraints.CT01_Abstract

namespace ToeFormal
namespace Constraints

open ToeFormal.CPNLSE2D

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/--
CP-NLSE instance-layer corollary:

Re-exports the CT-01 bridge theorem in the CP-NLSE packaging layer.
This keeps the proof in CT01_Abstract and provides a stable import surface
for downstream modules.
-/
theorem CT01_CPNLSE2D_noLinearPartAt0_preserves_DR01_onPlaneWaves
  (LP : LinearizationAt0_WithProbeSound)
  (hProbe : LP.Probe = PlaneWaveProbe)
  (P : Field2D → Field2D)
  (hNL : NoLinearPartAt0_Field2D LP.L P) :
  PreservesDR01_onPlaneWaves P :=
by
  simpa [NoLinearPartAt0_Abstract] using
    (CT01_noLinearPartAt0_preserves_DR01_onPlaneWaves
      (LP := LP) (hProbe := hProbe) (P := P) (hNL := hNL))

end

end Constraints
end ToeFormal
