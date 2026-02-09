/-
ToeFormal/Constraints/CT01_Abstract.lean

CT-01 scaffold: abstract “no linear part at ψ = 0” + probe-family surrogate.
Wires the plane-wave preservation predicate to PhaseB reduction lemma
and the plane-wave unperturbed reduction lemma.
-/

import Mathlib
import ToeFormal.CPNLSE2D.Dispersion
import ToeFormal.CPNLSE2D.PlaneWaveOperators
import ToeFormal.CPNLSE2D.PhaseB.DispersionPreservation
import ToeFormal.Constraints.CT01_LinearizationInterface
import ToeFormal.Constraints.CT01_LinearizationInterfaceProbe

namespace ToeFormal
namespace Constraints

open ToeFormal.CPNLSE2D

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A perturbation is an extra term mapping fields to fields. -/
abbrev Perturbation := Field2D → Field2D

/-- Abstract notion of “no linear part at ψ = 0” (structural-only), parameterized
by a chosen linearization interface (see `CT01_LinearizationInterface`). -/
abbrev NoLinearPartAt0_Abstract (L : LinearizationAt0_Field2D) (P : Perturbation) : Prop :=
  NoLinearPartAt0_Field2D L P

/-- Probe-family surrogate: perturbation vanishes on plane waves. -/
def NoLinearPartOnPlaneWaves (P : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ), P (planeWave A kx ky) = 0

/--
Coefficient-equality reduction target actually used by PhaseB:

Either the scalar coefficients match, or the plane wave value is zero (pointwise).
-/
def EQ02CoeffTarget (A : ℂ) (kx ky : ℝ) : Prop :=
  ∀ x y t : ℝ, (omega kx ky : ℂ) = eigC kx ky ∨ planeWave A kx ky x y t = 0

/--
“DR-01 unchanged on plane waves” (structural wrapper form):
perturbed EQ-02 is equivalent to unperturbed EQ-02 on the probe family.
-/
def PreservesDR01_onPlaneWaves (P : Perturbation) : Prop :=
  ∀ (A : ℂ) (kx ky : ℝ),
    EQ02PertHolds P (planeWave A kx ky) ↔ EQ02Holds (planeWave A kx ky)

/--
CT-01 probe-family theorem:

NOTE: PhaseB requires `AdmissibleOnPlaneWave P`. Until you can derive that from
your “no linear part” criterion, we take it as an explicit hypothesis here.
-/
theorem CT01_noLinearPartOnPlaneWaves_preserves_DR01
  (P : Perturbation)
  (hPW : NoLinearPartOnPlaneWaves P)
  (hAdm : AdmissibleOnPlaneWave P) :
  PreservesDR01_onPlaneWaves P := by
  intro A kx ky
  -- Scaffold hook: keep hPW in the statement even though not yet used.
  have _hPW : NoLinearPartOnPlaneWaves P := hPW
  -- PhaseB: perturbed EQ-02 on plane waves reduces to the coeff-target.
  have hPert :
      EQ02PertHolds P (planeWave A kx ky) ↔ EQ02CoeffTarget A kx ky := by
    simpa [EQ02CoeffTarget] using
      (EQ02Pert_planeWave_reduces_to_same_coeff_equality (P := P) hAdm A kx ky)
  -- Unperturbed: EQ-02 on plane waves reduces to the same coeff-target.
  have hUnpert :
      EQ02Holds (planeWave A kx ky) ↔ EQ02CoeffTarget A kx ky := by
    -- If this lemma’s RHS is not *definitionally* the same, adjust EQ02CoeffTarget accordingly.
    simpa [EQ02CoeffTarget] using
      (EQ02Holds_planeWave_iff (A := A) (kx := kx) (ky := ky))
  -- Conclude perturbed ↔ unperturbed via the shared target.
  constructor
  · intro h
    exact (hUnpert.mpr (hPert.mp h))
  · intro h
    exact (hPert.mpr (hUnpert.mp h))

/--
CT-01 abstract criterion ⇒ plane-wave probe preservation (DR-01 unchanged on plane waves).

This is the requested “Step 1→2 bridge”:
- uses the abstract `NoLinearPartAt0_Abstract` (now meaningful via probe-soundness)
- derives `NoLinearPartOnPlaneWaves`
- derives the Phase-B admissibility hypothesis `AdmissibleOnPlaneWave`
- reuses `CT01_noLinearPartOnPlaneWaves_preserves_DR01`
-/
theorem CT01_noLinearPartAt0_preserves_DR01_onPlaneWaves
  (LP : LinearizationAt0_WithProbeSound)
  (hProbe : LP.Probe = PlaneWaveProbe)
  (P : Perturbation)
  (hNL : NoLinearPartAt0_Abstract LP.L P) :
  PreservesDR01_onPlaneWaves P := by
  -- 1) get Field2D-level vanishing on plane waves from probe-soundness
  have hPW_fun : ∀ (A : ℂ) (kx ky : ℝ), P (planeWave A kx ky) = 0 := by
    exact noLinearPartAt0_implies_vanishes_onPlaneWaves (LP := LP) hProbe P hNL
  -- 2) convert to your existing probe-family surrogate form
  have hPW : NoLinearPartOnPlaneWaves P := by
    intro A kx ky
    exact hPW_fun A kx ky
  -- 3) derive Phase-B admissibility (pointwise) from Field2D equality
  have hAdm : AdmissibleOnPlaneWave P := by
    intro A kx ky x y t
    have h0 : P (planeWave A kx ky) = 0 := hPW_fun A kx ky
    simpa using congrArg (fun f => f x y t) h0
  -- 4) reuse existing CT01 wiring theorem
  exact CT01_noLinearPartOnPlaneWaves_preserves_DR01 (P := P) hPW hAdm


end
end Constraints
end ToeFormal
