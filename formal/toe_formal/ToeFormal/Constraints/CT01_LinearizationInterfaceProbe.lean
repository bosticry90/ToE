import Mathlib
import ToeFormal.Constraints.CT01_LinearizationInterface
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs

namespace ToeFormal
namespace Constraints

open ToeFormal.CPNLSE2D

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/--
Probe-sound linearization interface.

This is structural-only. It does *not* define analytic linearization.
It packages:
- an abstract linearization extractor `L : LinearizationAt0_Field2D`
- a probe predicate `Probe : Field2D → Prop`
- a soundness axiom stating: if the extracted linear part at 0 is zero,
  then the perturbation vanishes on the probe family.
-/
structure LinearizationAt0_WithProbeSound where
  L : LinearizationAt0_Field2D
  Probe : Field2D → Prop
  sound :
    ∀ (P : Field2D → Field2D),
      NoLinearPartAt0_Field2D L P →
      ∀ ψ : Field2D, Probe ψ → P ψ = 0

/-- The canonical plane-wave probe predicate, expressed as an existential. -/
def PlaneWaveProbe : Field2D → Prop :=
  fun ψ => ∃ (A : ℂ) (kx ky : ℝ), ψ = planeWave A kx ky

/--
Specialized soundness lemma for the plane-wave family:
if the linear part at 0 is zero, then the perturbation vanishes on plane waves
(as a *Field2D equality*).
-/
lemma noLinearPartAt0_implies_vanishes_onPlaneWaves
  (LP : LinearizationAt0_WithProbeSound)
  (hProbe : LP.Probe = PlaneWaveProbe)
  (P : Field2D → Field2D)
  (hNL : NoLinearPartAt0_Field2D LP.L P) :
  ∀ (A : ℂ) (kx ky : ℝ), P (planeWave A kx ky) = 0 := by
  intro A kx ky
  have : LP.Probe (planeWave A kx ky) := by
    -- construct the canonical witness and substitute using `hProbe`
    exact (hProbe ▸ (by refine ⟨A, kx, ky, rfl⟩))
  -- apply probe-soundness
  exact LP.sound P hNL (planeWave A kx ky) this

end
end Constraints
end ToeFormal
