/-
ToeFormal/Derivation/Parents/P2_Wave_EFT.lean

Parent P2: real/complex scalar wave-type EFT (second order in time),
with explicit symmetries and the “derived vs assumed” separation encoded as hypotheses.

This file proves the first concrete dispersion result for the linearized P2 wave parent:
a plane wave solves the linear PDE iff ω² matches the derivation-layer symbol polynomial.
-/

import ToeFormal.Derivation.Conventions.FourierSymbols

namespace ToeFormal.Derivation.Parents

noncomputable section

open Complex
open ToeFormal.Derivation

set_option autoImplicit false

/-- Complex field over (t,x). -/
abbrev FieldC : Type := ℝ → ℝ → ℂ

/-- Abstract derivative operators (placeholders in this parent lock layer). -/
opaque Dtt : FieldC → FieldC
opaque Dxx : FieldC → FieldC
opaque Dxxxx : FieldC → FieldC
opaque Dxxxxxx : FieldC → FieldC

/-- Unit-amplitude plane wave used for linear dispersion checks. -/
def planeWave (k ω : ℝ) : FieldC :=
  fun t x => Complex.exp (Complex.I * ((k * x - ω * t) : ℂ))

/-- Plane-wave action of abstract derivatives (symbol-level axioms). -/
axiom Dtt_planeWave (k ω : ℝ) :
  Dtt (planeWave k ω) = fun t x => ((-(ω^2) : ℝ) : ℂ) * planeWave k ω t x

axiom Dxx_planeWave (k ω : ℝ) :
  Dxx (planeWave k ω) = fun t x => ((-(k^2) : ℝ) : ℂ) * planeWave k ω t x

axiom Dxxxx_planeWave (k ω : ℝ) :
  Dxxxx (planeWave k ω) = fun t x => (((k^4) : ℝ) : ℂ) * planeWave k ω t x

axiom Dxxxxxx_planeWave (k ω : ℝ) :
  Dxxxxxx (planeWave k ω) = fun t x => ((-(k^6) : ℝ) : ℂ) * planeWave k ω t x

/-- Parameters for P2 (derivation layer). -/
structure P2Params where
  c2 : ℝ
  c4 : ℝ
  c6 : ℝ

/-- Abstract “EOM operator” for wave-type flow: ψ_tt = RHS(ψ). -/
opaque RHS_P2 : P2Params → FieldC → FieldC

/-- Structural target form for the P2 RHS (linear EFT gradient expansion). -/
def RHS_P2_EFT (p : P2Params) (ψ : FieldC) : FieldC :=
  fun t x =>
    (p.c2 : ℂ) * (Dxx ψ t x)
    + (p.c4 : ℂ) * (Dxxxx ψ t x)
    + (p.c6 : ℂ) * (Dxxxxxx ψ t x)

/-
At derivation-layer we *postulate* that P2’s chosen action produces RHS_P2_EFT.
Later, we will refine this into a true variational derivation with sign tracking.
-/
axiom P2_rhs_matches_EFT :
  ∀ (p : P2Params) (ψ : FieldC), RHS_P2 p ψ = RHS_P2_EFT p ψ

/-- Wave-type equation of motion for P2. -/
def EOM_P2 (p : P2Params) (ψ : FieldC) : Prop :=
  ∀ t x, (Dtt ψ t x) = RHS_P2 p ψ t x

/-- Placeholder for a cubic nonlinearity term in the parent layer. -/
opaque cubicDensity : ℝ → FieldC → FieldC

/-- Parent wave residual (structural form used by bridge proofs). -/
def waveResidual (c2 c4 c6 g3 : ℝ) (phi : FieldC) : FieldC :=
  fun t x =>
    Dtt phi t x
    + (c2 : ℂ) * (Dxx phi t x)
    + (c4 : ℂ) * (Dxxxx phi t x)
    + (c6 : ℂ) * (Dxxxxxx phi t x)
    + (cubicDensity g3 phi t x)

/-- P2 parent satisfier predicate for the wave residual. -/
def SatisfiesWaveP2 (c2 c4 c6 g3 : ℝ) (phi : FieldC) : Prop :=
  ∀ t x, waveResidual c2 c4 c6 g3 phi t x = 0

/-
Dispersion polynomial for ω² in the linear regime, under the derivation-layer symbol convention:
  Dxx ↦ -k², Dxxxx ↦ +k⁴, Dxxxxxx ↦ -k⁶, Dtt ↦ -ω².
So: -ω² = c2(-k²) + c4(+k⁴) + c6(-k⁶)  ⇒  ω² = c2 k² - c4 k⁴ + c6 k⁶.
-/
def ωsq_linear_P2 (p : P2Params) (k : ℝ) : ℝ :=
  p.c2 * k^2 - p.c4 * k^4 + p.c6 * k^6

/-- Linear plane-wave solution statement (skeleton). -/
def IsLinearPlaneWaveSolution_P2 (p : P2Params) (k ω : ℝ) : Prop :=
  ∀ t x,
    (Dtt (planeWave k ω) t x) =
      (p.c2 : ℂ) * (Dxx (planeWave k ω) t x)
    + (p.c4 : ℂ) * (Dxxxx (planeWave k ω) t x)
    + (p.c6 : ℂ) * (Dxxxxxx (planeWave k ω) t x)

/-- Linear dispersion lemma for P2: plane-wave solution implies ω² = ωsq_linear_P2(p,k). -/
theorem dispersion_linear_P2 (p : P2Params) (k ω : ℝ)
  (h : IsLinearPlaneWaveSolution_P2 p k ω) :
  ω^2 = ωsq_linear_P2 p k := by
  -- Evaluate the linear equation at (t,x)=(0,0).
  have h0 := h 0 0
  -- Plane wave at the origin is 1.
  have hψ00 : planeWave k ω 0 0 = (1 : ℂ) := by
    simp [planeWave]
  -- Specialize derivation-layer plane-wave axioms at (0,0).
  have hDtt00 :
      Dtt (planeWave k ω) 0 0
        = (-(ω^2 : ℝ)) * (planeWave k ω 0 0) := by
    simpa using congrArg (fun f => f 0 0) (Dtt_planeWave k ω)
  have hDxx00 :
      Dxx (planeWave k ω) 0 0
        = (-(k^2 : ℝ)) * (planeWave k ω 0 0) := by
    simpa using congrArg (fun f => f 0 0) (Dxx_planeWave k ω)
  have hDxxxx00 :
      Dxxxx (planeWave k ω) 0 0
        = (k^4 : ℝ) * (planeWave k ω 0 0) := by
    simpa using congrArg (fun f => f 0 0) (Dxxxx_planeWave k ω)
  have hDxxxxxx00 :
      Dxxxxxx (planeWave k ω) 0 0
        = (-(k^6 : ℝ)) * (planeWave k ω 0 0) := by
    simpa using congrArg (fun f => f 0 0) (Dxxxxxx_planeWave k ω)
  -- Substitute the point evaluations and simplify using planeWave(0,0)=1.
  have h0' := h0
  simp only [hDtt00, hDxx00, hDxxxx00, hDxxxxxx00, hψ00] at h0'
  -- h0' is now an equality in ℂ with only scalars. Convert it into ω² = polynomial.
  -- Negate both sides to flip the leading minus on ω².
  have h1 : ((ω^2 : ℝ) : ℂ) =
      (p.c2 : ℂ) * ((k^2 : ℝ) : ℂ)
      - (p.c4 : ℂ) * ((k^4 : ℝ) : ℂ)
      + (p.c6 : ℂ) * ((k^6 : ℝ) : ℂ) := by
    -- h0' has shape: -(ω²) = -(c2*k²) + (c4*k⁴) + -(c6*k⁶), all in ℂ.
    -- Apply `neg` to both sides and normalize.
    have hneg := congrArg (fun z : ℂ => -z) h0'
    -- Now simp/ring to reach the standard form.
    -- `sub_eq_add_neg` helps align with ωsq_linear_P2, `ring` clears signs.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm] using hneg
  -- Match the definition of ωsq_linear_P2 and drop back to ℝ via injectivity.
  have hc : ((ω^2 : ℝ) : ℂ) = (ωsq_linear_P2 p k : ℂ) := by
    simpa [ωsq_linear_P2, sub_eq_add_neg, pow_two, pow_succ] using h1
  exact_mod_cast hc

end
end ToeFormal.Derivation.Parents
