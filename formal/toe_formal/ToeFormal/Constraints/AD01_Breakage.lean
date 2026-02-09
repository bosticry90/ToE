import ToeFormal.Constraints.AD01_AdmissibleOp
import ToeFormal.OperatorCore.PlaneWaveEigenstructure
import ToeFormal.OperatorCore.OperatorSignature
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs

namespace ToeFormal
namespace Constraints
namespace AD01

open ToeFormal
open ToeFormal.OperatorCore
open ToeFormal.CPNLSE2D

/-
AD01 Breakage Lemma (probe-relative)

This theorem is the AD-01 wiring of OP-PW-04:
If O and O+E are dispersion-compatible on plane-wave probes,
then E vanishes on plane-wave probes.

This is structural only. No analytic PDE claims.
-/

-- You likely already have Op2D and DispersionCompatible in OP-SIG-01.
-- The goal is to reuse the canonical lemma noted in OP-PW-04:
--   dispersionCompatible_add_implies_E_vanishes_on_planeWaves_fun

theorem admissibleOp_breakage_onPlaneWaves
  (O E : Op2D)
  (hO : DispersionCompatible O)
  (hOE : DispersionCompatible (O + E))
  :
  ∀ (A : ℂ) (kx ky : ℝ),
    E.Op (planeWave A kx ky) = 0 := by
  intro A kx ky
  simpa using
    dispersionCompatible_add_implies_E_vanishes_on_planeWaves_fun
      (O := O) (E := E) hO hOE A kx ky

end AD01
end Constraints
end ToeFormal
