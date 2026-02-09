/-
ToeFormal/Constraints/CT01_LinearizationAt0.lean

Purpose:
- Introduce a structural "LinearizationAt0" bridge without analytic derivatives.
- Keep it probe-relative: it only talks about the plane-wave probe family.
- Show: if the (axiomatized) linearization L0 matches P on probes and L0 vanishes on probes,
  then P is AdmissibleOnPlaneWave, and CT-01 preservation follows by existing Phase A3 + Phase B.

No physical claims.
-/

import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperators
import ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToeFormal
namespace Constraints

open ToeFormal.CPNLSE2D

/-- CT-01 preservation predicate (probe-family form). -/
def PreservesDR01_onPlaneWaves (P : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ),
    EQ02PertHolds P (planeWave A kx ky) ↔ EQ02Holds (planeWave A kx ky)

/--
Abstract "linearization at 0" bridge (probe-relative, structural):

`LinearizationAt0 P L0` means: on the plane-wave probes, P behaves exactly like L0.
This is an axiomatized surrogate for "first-order term".
-/
def LinearizationAt0 (P L0 : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ) (x y t : ℝ),
    P (planeWave A kx ky) x y t = L0 (planeWave A kx ky) x y t

/-- "No linear part at 0" (probe-relative, structural): L0 vanishes on plane-wave probes. -/
def NoLinearPartAt0 (L0 : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ) (x y t : ℝ),
    L0 (planeWave A kx ky) x y t = 0

/--
Bridge lemma:
If P matches its linearization L0 on probes, and L0 vanishes on probes,
then P is admissible on probes (Phase B notion).
-/
theorem linearization_zero_implies_admissible
  (P L0 : Perturbation)
  (hLin : LinearizationAt0 P L0)
  (h0 : NoLinearPartAt0 L0) :
  AdmissibleOnPlaneWave P := by
  intro A kx ky x y t
  calc
    P (planeWave A kx ky) x y t
        = L0 (planeWave A kx ky) x y t := by
            exact hLin A kx ky x y t
    _ = 0 := by
            exact h0 A kx ky x y t

/--
CT-01b (structural, probe-relative, via LinearizationAt0):

If P has a probe-relative linearization L0 and that linearization is zero on probes,
then DR-01 is unchanged on plane-wave probes (EQ02PertHolds ↔ EQ02Holds).
-/
theorem CT01b_linearizationAt0_zero_preserves_DR01
  (P L0 : Perturbation)
  (hLin : LinearizationAt0 P L0)
  (h0 : NoLinearPartAt0 L0) :
  PreservesDR01_onPlaneWaves P := by
  have hP : AdmissibleOnPlaneWave P :=
    linearization_zero_implies_admissible P L0 hLin h0
  intro A kx ky
  have hPert :=
    (EQ02Pert_planeWave_reduces_to_same_coeff_equality P hP A kx ky)
  have hUn :=
    (EQ02Holds_planeWave_iff A kx ky)
  simpa [PreservesDR01_onPlaneWaves] using (hPert.trans hUn.symm)

end Constraints
end ToeFormal
