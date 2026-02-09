import Mathlib
import ToeFormal.CPNLSE2D.PlaneWaveOperatorDefs
import ToeFormal.Constraints.FN01_DeformationClass

namespace ToeFormal
namespace Constraints
namespace FN01

open ToeFormal.CPNLSE2D
open ToeFormal.Constraints

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Canonical SYM-01 phase action on `Field2D`: multiply the field by `exp(i θ)` pointwise. -/
noncomputable def A0 : SYM01.PhaseAction Field2D where
  act θ ψ :=
    fun x y t => Complex.exp (Complex.I * (θ : ℂ)) * ψ x y t
  act_zero := by
    intro ψ
    funext x y t
    simp
  act_add := by
    intro θ₁ θ₂ ψ
    funext x y t
    simp [mul_add, Complex.exp_add, mul_assoc]

/-
FN-01 candidate membership lemmas (front-door entry points).

Purpose:
- Provide named candidate perturbations corresponding to the Python candidate table.
- Provide explicit per-candidate lemmas that either:
  (a) build `FN01_DeformationClass` from the three gate predicates, or
  (b) mark a candidate rejected by exhibiting a violated gate.

Design note:
- Most candidates cannot be structurally decided in Lean without additional axioms
  about the linearization extractor `L` and the operator semantics. For these, we
  provide cheap packaging lemmas that require the gate predicates as hypotheses.
- We *can* reject constant sources via `NoForcingAt0`, and we can reject
  complex conjugation w.r.t. the canonical phase action `AD01.A0`.
-/

/-- Representative: cubic nonlinearity `g * |ψ|^2 * ψ` (pointwise). -/
noncomputable def P_cubic (g : ℂ) : Perturbation :=
  fun ψ => fun x y t =>
    g * ((Complex.normSq (ψ x y t)) : ℂ) * (ψ x y t)

/-- Representative: complex conjugation (anti-linear). -/
noncomputable def P_conj : Perturbation :=
  fun ψ => fun x y t => star (ψ x y t)

/-- Representative: coordinate-multiplication `x * ψ` (breaks translation invariance). -/
noncomputable def P_xpsi : Perturbation :=
  fun ψ => fun x y t => (x : ℂ) * (ψ x y t)

/-- Representative: Laplacian surrogate `Δ ψ` (linear). -/
noncomputable def P_lap : Perturbation :=
  fun ψ => Delta ψ

/-- Representative: `∂xx ψ` surrogate (linear). -/
noncomputable def P_dxx : Perturbation :=
  fun ψ => Dxx ψ

/-- Representative: anisotropic linear term `∂xx ψ - ∂yy ψ`. -/
noncomputable def P_dxx_minus_dyy : Perturbation :=
  fun ψ => fun x y t => (Dxx ψ x y t) - (Dyy ψ x y t)

/-- Representative: constant source term (violates `NoForcingAt0` when nonzero). -/
noncomputable def P_constant_source (C : ℂ) : Perturbation :=
  fun _ψ => fun _x _y _t => C


/-
Cheap “admission” lemmas: these are the required front-door entry points.
They force any downstream theorem to either:
- provide the three gate predicates, or
- use an explicit rejection lemma.
-/

theorem P_cubic_isDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (g : ℂ)
    (hNoForcing : NoForcingAt0 (P_cubic g))
    (hPhase : SYM01.PhaseInvariant A (P_cubic g))
    (hNL : NoLinearPartAt0_Abstract L (P_cubic g)) :
    FN01_DeformationClass A L (P_cubic g) := by
  exact And.intro hNoForcing (And.intro hPhase hNL)


theorem P_xpsi_isDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (hNoForcing : NoForcingAt0 P_xpsi)
    (hPhase : SYM01.PhaseInvariant A P_xpsi)
    (hNL : NoLinearPartAt0_Abstract L P_xpsi) :
    FN01_DeformationClass A L P_xpsi := by
  exact And.intro hNoForcing (And.intro hPhase hNL)


theorem P_lap_isDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (hNoForcing : NoForcingAt0 P_lap)
    (hPhase : SYM01.PhaseInvariant A P_lap)
    (hNL : NoLinearPartAt0_Abstract L P_lap) :
    FN01_DeformationClass A L P_lap := by
  exact And.intro hNoForcing (And.intro hPhase hNL)


theorem P_dxx_isDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (hNoForcing : NoForcingAt0 P_dxx)
    (hPhase : SYM01.PhaseInvariant A P_dxx)
    (hNL : NoLinearPartAt0_Abstract L P_dxx) :
    FN01_DeformationClass A L P_dxx := by
  exact And.intro hNoForcing (And.intro hPhase hNL)


theorem P_dxx_minus_dyy_isDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (hNoForcing : NoForcingAt0 P_dxx_minus_dyy)
    (hPhase : SYM01.PhaseInvariant A P_dxx_minus_dyy)
    (hNL : NoLinearPartAt0_Abstract L P_dxx_minus_dyy) :
    FN01_DeformationClass A L P_dxx_minus_dyy := by
  exact And.intro hNoForcing (And.intro hPhase hNL)


/-
Explicit rejections for candidates that violate a gate definitionally.
-/

theorem P_constant_source_noForcingAt0_iff (C : ℂ) :
    NoForcingAt0 (P_constant_source C) ↔ C = 0 := by
  constructor
  · intro h
    -- Evaluate the function equality at a point.
    have h0 := congrArg (fun f => f 0 0 0) h
    simpa [P_constant_source] using h0
  · intro hC
    -- If C = 0, then the perturbation is identically zero.
    subst hC
    ext x y t
    simp [P_constant_source]


theorem P_constant_source_notDeformation
    (A : SYM01.PhaseAction Field2D)
    (L : LinearizationAt0_Field2D)
    (C : ℂ)
    (hC : C ≠ 0) :
    ¬ FN01_DeformationClass A L (P_constant_source C) := by
  intro h
  have hNoForcing : NoForcingAt0 (P_constant_source C) := h.1
  have hEq : C = 0 := (P_constant_source_noForcingAt0_iff (C := C)).1 hNoForcing
  exact hC hEq


/-- Conjugation is not phase-equivariant under the canonical phase action `A0`. -/
theorem P_conj_notPhaseInvariant_under_A0 :
  ¬ SYM01.PhaseInvariant A0 P_conj := by
  intro hInv
  -- Counterexample: ψ ≡ 1 and θ = π/2.
  let ψ : Field2D := fun _x _y _t => (1 : ℂ)
  let θ : ℝ := Real.pi / 2
  have h := hInv (θ := θ) (ψ := ψ)
  have h0 := congrArg (fun f => f 0 0 0) h
  -- Reduce the phase-equivariance condition at a point.
  have hEq : star (Complex.exp (Complex.I * (θ : ℂ))) = Complex.exp (Complex.I * (θ : ℂ)) := by
    simpa [SYM01.PhaseInvariant, A0, SYM01.PhaseAction.act, P_conj, ψ, θ, mul_assoc] using h0
  -- But exp(i π/2) = i, and conj(i) = -i.
  have hExp : Complex.exp (Complex.I * (θ : ℂ)) = Complex.I := by
    have : Complex.exp ((θ : ℂ) * Complex.I) = Complex.I := by
      -- exp(iθ) = cos θ + i sin θ.
      simp [Complex.exp_mul_I, θ]
    simpa [mul_comm] using this
  -- Contradiction: conj(exp(iθ)) = exp(iθ) would force -i = i.
  have : (-Complex.I) = Complex.I := by
    simpa [hExp] using hEq
  have hne : (-Complex.I) ≠ (Complex.I) := by
    simpa using (neg_ne_self.2 (by simp : (Complex.I : ℂ) ≠ 0))
  exact hne this


theorem P_conj_notDeformation_under_A0
    (L : LinearizationAt0_Field2D) :
    ¬ FN01_DeformationClass A0 L P_conj := by
  intro h
  have hPhase : SYM01.PhaseInvariant A0 P_conj := h.2.1
  exact P_conj_notPhaseInvariant_under_A0 hPhase


/-
Per-candidate DR-01 corollaries (one-liners).

These are the intended “consequence exports” that make the FN-01 → DR-01 path
repeatable per candidate.
-/

theorem preserves_DR01_onPlaneWaves_of_P_cubic
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (g : ℂ)
    (hNoForcing : NoForcingAt0 (P_cubic g))
    (hPhase : SYM01.PhaseInvariant A (P_cubic g))
    (hNL : NoLinearPartAt0_Abstract LP.L (P_cubic g)) :
    PreservesDR01_onPlaneWaves (P_cubic g) := by
  exact
    preserves_DR01_onPlaneWaves_of_deformationClass
      (LP := LP)
      (hProbe := hProbe)
      (A := A)
      (P := P_cubic g)
      (hFN := P_cubic_isDeformation (A := A) (L := LP.L) (g := g) hNoForcing hPhase hNL)


theorem preserves_DR01_onPlaneWaves_of_P_xpsi
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (hNoForcing : NoForcingAt0 P_xpsi)
    (hPhase : SYM01.PhaseInvariant A P_xpsi)
    (hNL : NoLinearPartAt0_Abstract LP.L P_xpsi) :
    PreservesDR01_onPlaneWaves P_xpsi := by
  exact
    preserves_DR01_onPlaneWaves_of_deformationClass
      (LP := LP)
      (hProbe := hProbe)
      (A := A)
      (P := P_xpsi)
      (hFN := P_xpsi_isDeformation (A := A) (L := LP.L) hNoForcing hPhase hNL)


theorem preserves_DR01_onPlaneWaves_of_P_lap
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (hNoForcing : NoForcingAt0 P_lap)
    (hPhase : SYM01.PhaseInvariant A P_lap)
    (hNL : NoLinearPartAt0_Abstract LP.L P_lap) :
    PreservesDR01_onPlaneWaves P_lap := by
  exact
    preserves_DR01_onPlaneWaves_of_deformationClass
      (LP := LP)
      (hProbe := hProbe)
      (A := A)
      (P := P_lap)
      (hFN := P_lap_isDeformation (A := A) (L := LP.L) hNoForcing hPhase hNL)


theorem preserves_DR01_onPlaneWaves_of_P_dxx
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (hNoForcing : NoForcingAt0 P_dxx)
    (hPhase : SYM01.PhaseInvariant A P_dxx)
    (hNL : NoLinearPartAt0_Abstract LP.L P_dxx) :
    PreservesDR01_onPlaneWaves P_dxx := by
  exact
    preserves_DR01_onPlaneWaves_of_deformationClass
      (LP := LP)
      (hProbe := hProbe)
      (A := A)
      (P := P_dxx)
      (hFN := P_dxx_isDeformation (A := A) (L := LP.L) hNoForcing hPhase hNL)


theorem preserves_DR01_onPlaneWaves_of_P_dxx_minus_dyy
    (LP : LinearizationAt0_WithProbeSound)
    (hProbe : LP.Probe = PlaneWaveProbe)
    (A : SYM01.PhaseAction Field2D)
    (hNoForcing : NoForcingAt0 P_dxx_minus_dyy)
    (hPhase : SYM01.PhaseInvariant A P_dxx_minus_dyy)
    (hNL : NoLinearPartAt0_Abstract LP.L P_dxx_minus_dyy) :
    PreservesDR01_onPlaneWaves P_dxx_minus_dyy := by
  exact
    preserves_DR01_onPlaneWaves_of_deformationClass
      (LP := LP)
      (hProbe := hProbe)
      (A := A)
      (P := P_dxx_minus_dyy)
      (hFN := P_dxx_minus_dyy_isDeformation (A := A) (L := LP.L) hNoForcing hPhase hNL)

end
end FN01
end Constraints
end ToeFormal
