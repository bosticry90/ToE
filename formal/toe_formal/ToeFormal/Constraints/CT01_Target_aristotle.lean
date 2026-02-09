/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f43cd06c-7ee1-4e7a-bf25-8416190fb1d1

Aristotle encountered an error while processing imports for this file.
Error:
Axioms were added during init_sorries: ['ToeFormal.CPNLSE2D.Delta_planeWave', 'ToeFormal.CPNLSE2D.Dt_planeWave']
-/

/-
ToeFormal/Constraints/CT01_Target.lean

CT-01 (structural, probe-relative):

AdmissibleOnPlaneWave P  ⇒  adding P does not change the DR-01 reduction target
for EQ-02 when evaluated on the plane-wave probe family.

Formally, for all plane waves:
  EQ02PertHolds P (planeWave A kx ky) ↔ EQ02Holds (planeWave A kx ky)

Dependencies (by import):
- ToeFormal.CPNLSE2D.PlaneWaveOperators (defines EQ02Holds and the plane-wave reduction lemma)
- ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation (defines EQ02PertHolds, AdmissibleOnPlaneWave,
  and the Phase-B preservation lemma)
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

/--
CT-01 preservation predicate (probe-family form):

On plane-wave probes, the perturbed EQ-02 is equivalent to the unperturbed EQ-02.
-/
def PreservesDR01_onPlaneWaves (P : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ),
    EQ02PertHolds P (planeWave A kx ky) ↔ EQ02Holds (planeWave A kx ky)

/--
CT-01 target theorem:

If P contributes zero on the plane-wave probe family (probe-relative “no linear part at ψ=0”),
then DR-01 is unchanged on plane waves, in the sense that EQ-02 holds on a plane wave
iff the perturbed EQ-02 holds on that plane wave.
-/
theorem CT01_noLinearPart_preserves_DR01
  (P : Perturbation)
  (hP : AdmissibleOnPlaneWave P) :
  PreservesDR01_onPlaneWaves P := by
  intro A kx ky
  -- Phase B: perturbed equation reduces to the same coefficient-equality-times-planeWave target
  have hPert :=
    (EQ02Pert_planeWave_reduces_to_same_coeff_equality P hP A kx ky)
  -- Phase A3: unperturbed equation reduces to the same coefficient-equality-times-planeWave target
  have hUn :=
    (EQ02Holds_planeWave_iff A kx ky)
  -- Combine the two reductions
  simpa [PreservesDR01_onPlaneWaves] using (hPert.trans hUn.symm)

end Constraints
end ToeFormal
