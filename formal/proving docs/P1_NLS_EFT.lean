/-
ToeFormal/Derivation/Parents/P1_NLS_EFT.lean

Parent P1: nonrelativistic complex scalar EFT (Schrödinger/GPE + gradient expansion),
with explicit symmetries and the “derived vs assumed” separation encoded as hypotheses.

This is a Lean *skeleton*: it defines the objects we will later connect to LOCK modules
via bridge lemmas. It does not attempt full functional-analytic variational calculus yet.
-/

import ToeFormal.Derivation.Conventions.FourierSymbols

namespace ToeFormal.Derivation.Parents

noncomputable section

open Complex
open ToeFormal.Derivation

/-- Parameters for P1 (derivation layer). -/
structure P1Params where
  g : ℝ
  lam : ℝ
  beta : ℝ

/-- Abstract “EOM operator” for Schrödinger-type flow: i ψ_t = RHS(ψ). -/
opaque RHS_P1 : P1Params → FieldC → FieldC

/--
Structural target form for the first-order-in-time UCFF-like RHS (linear part only for now).

Nonlinear term `g |ψ|^2 ψ` is intentionally omitted here because the first “real proof”
targets *linear* dispersion and assumes `p.g = 0` anyway.
-/
def RHS_P1_EFT (p : P1Params) (ψ : FieldC) : FieldC :=
  fun t x =>
    (-(1/2 : ℝ) : ℂ) * (Dxx ψ t x)
    + (p.lam : ℂ) * (Dxxxx ψ t x)
    + (p.beta : ℂ) * (Dxxxxxx ψ t x)

/-
At derivation-layer we *postulate* that P1’s chosen action/hamiltonian produces RHS_P1_EFT.
Later, we will refine this into (i) a Hamiltonian definition, and (ii) lemmas showing that
its variational derivative yields these terms (including the integration-by-parts signs).
-/
axiom P1_rhs_matches_EFT :
  ∀ (p : P1Params) (ψ : FieldC), RHS_P1 p ψ = RHS_P1_EFT p ψ

/-- Schrödinger-type equation of motion for P1. -/
def EOM_P1 (p : P1Params) (ψ : FieldC) : Prop :=
  ∀ t x, Complex.I * (Dt ψ t x) = RHS_P1 p ψ t x

/-
Linear dispersion in the vacuum / linear regime.
This matches the derivation-layer symbol convention:
  Dxx ↦ -k^2, Dxxxx ↦ +k^4, Dxxxxxx ↦ -k^6.
-/
def omega_linear_P1 (p : P1Params) (k : ℝ) : ℝ :=
  (1/2) * k^2 + p.lam * k^4 - p.beta * k^6

/-- Linear plane-wave solution statement (skeleton). -/
def IsLinearPlaneWaveSolution (p : P1Params) (k ω : ℝ) : Prop :=
  let ψ := planeWave k ω
  (p.g = 0) ∧
  (∀ t x, Complex.I * (Dt ψ t x) =
    (-(1/2 : ℝ) : ℂ) * (Dxx ψ t x)
    + (p.lam : ℂ) * (Dxxxx ψ t x)
    + (p.beta : ℂ) * (Dxxxxxx ψ t x))

/-
Dispersion lemma in derivation-layer convention:
If ψ = exp(i(kx - ωt)) solves the linear equation, then ω = omega_linear_P1(p,k).
-/
theorem dispersion_linear_P1 (p : P1Params) (k ω : ℝ)
  (h : IsLinearPlaneWaveSolution p k ω) :
  ω = omega_linear_P1 p k := by
  rcases h with ⟨hg, hlin⟩

  -- Evaluate the linear equation at (t,x)=(0,0).
  have h0 := hlin 0 0

  -- Plane wave at the origin is 1.
  have hψ00 : planeWave k ω 0 0 = (1 : ℂ) := by
    simp [ToeFormal.Derivation.planeWave]

  -- Specialize the derivation-layer plane-wave axioms at (0,0).
  have hDt00 :
      Dt (planeWave k ω) 0 0
        = (-(Complex.I) * (ω : ℂ)) * (planeWave k ω 0 0) := by
    simpa using congrArg (fun f => f 0 0) (Dt_planeWave k ω)

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

  -- Key simplification lemma: -(I * (I * z)) = z in ℂ.
  have hII (z : ℂ) : -(Complex.I * (Complex.I * z)) = z := by
    calc
      -(Complex.I * (Complex.I * z))
          = -((Complex.I * Complex.I) * z) := by
              simp [← mul_assoc]
      _ = -((-1 : ℂ) * z) := by
              simp [Complex.I_mul_I]
      _ = z := by
              ring

  -- Rewrite h0 into a scalar identity in ℂ and normalize.
  have hc : (ω : ℂ) = (omega_linear_P1 p k : ℂ) := by
    have h0' := h0
    -- Replace derivatives at (0,0) and planeWave(0,0)=1.
    simp [hDt00, hDxx00, hDxxxx00, hDxxxxxx00, hψ00] at h0'
    -- Normalize the leftover `-(I*(I*ω))` and match omega_linear_P1.
    -- (h0' is an equality in ℂ.)
    have hω :
        (ω : ℂ) =
          (2⁻¹ : ℂ) * (k : ℂ) ^ 2
          + (p.lam : ℂ) * (k : ℂ) ^ 4
          + -((p.beta : ℂ) * (k : ℂ) ^ 6) := by
      simpa [hII] using h0'
    simpa [omega_linear_P1, sub_eq_add_neg, hg] using hω

  -- Coercions ℝ → ℂ are injective.
  exact_mod_cast hc

end
end ToeFormal.Derivation.Parents
