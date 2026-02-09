/-
ToeFormal/Derivation/Conventions/FourierSymbols.lean

Derivation-layer Fourier symbol convention (explicitly separate from locks).
Goal: provide a single, reusable convention for (∂x, ∂xx, ∂xxxx, …) acting on plane waves,
and a clean “symbol map” interface that downstream derivation proofs can use.

This file does NOT change any LOCK_* results. It is a derivation-layer convention sheet in Lean.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic

namespace ToeFormal.Derivation

noncomputable section

open Complex

/-- Space-time fields used in derivation layer (1D). -/
abbrev FieldC := ℝ → ℝ → ℂ   -- t ↦ x ↦ value
abbrev FieldR := ℝ → ℝ → ℝ

/-- Plane wave in 1D: exp(i (k x - ω t)). -/
def planeWave (k ω : ℝ) : FieldC :=
  fun t x => Complex.exp (Complex.I * (k * x - ω * t))

/-
Derivation-layer Fourier symbol convention:

For planeWave(k, ω), we adopt:
  Dx      ↦  i k
  Dxx     ↦ -k^2
  D(2n)   ↦ (-1)^n k^(2n)
  D(2n+1) ↦ i (-1)^n k^(2n+1)

This is declared here as axioms about *derivation-layer operators*.
Locks may use opaque derivative placeholders with their own operator semantics;
bridges later must map lock-operators to these symbols explicitly.
-/

/-- Derivation-layer spatial derivative operators (1D). -/
opaque Dx : FieldC → FieldC
opaque Dxx : FieldC → FieldC
opaque Dxxxx : FieldC → FieldC
opaque Dxxxxxx : FieldC → FieldC

/-- Derivation-layer time derivative operators (for envelope/Schr flows). -/
opaque Dt : FieldC → FieldC
opaque Dtt : FieldC → FieldC

/-- Symbol map: for each operator we can talk about its Fourier symbol σ(k). -/
structure SymbolicOp where
  op : FieldC → FieldC
  sigma : ℝ → ℂ

namespace SymbolicOp

/-- “op matches sigma” means: op acting on a plane wave multiplies by sigma(k). -/
def MatchesPlaneWave (S : SymbolicOp) : Prop :=
  ∀ (k ω : ℝ), S.op (planeWave k ω) = fun t x => (S.sigma k) * (planeWave k ω t x)

end SymbolicOp

/-
Axioms fixing the derivation-layer convention for the core spatial operators.
(We keep ω as a parameter but the spatial symbols depend only on k.)
-/
axiom Dx_planeWave :
  ∀ (k ω : ℝ), Dx (planeWave k ω) = fun t x => (Complex.I * k) * (planeWave k ω t x)

axiom Dxx_planeWave :
  ∀ (k ω : ℝ), Dxx (planeWave k ω) = fun t x => (-(k^2 : ℝ)) * (planeWave k ω t x)

axiom Dxxxx_planeWave :
  ∀ (k ω : ℝ), Dxxxx (planeWave k ω) = fun t x => (k^4 : ℝ) * (planeWave k ω t x)

axiom Dxxxxxx_planeWave :
  ∀ (k ω : ℝ), Dxxxxxx (planeWave k ω) = fun t x => (-(k^6 : ℝ)) * (planeWave k ω t x)

/-
Time derivative symbols:
  Dt planeWave  = (-i ω) planeWave
  Dtt planeWave = (-ω^2) planeWave
-/
axiom Dt_planeWave :
  ∀ (k ω : ℝ), Dt (planeWave k ω) = fun t x => (-(Complex.I) * ω) * (planeWave k ω t x)

axiom Dtt_planeWave :
  ∀ (k ω : ℝ), Dtt (planeWave k ω) = fun t x => (-(ω^2 : ℝ)) * (planeWave k ω t x)

end ToeFormal.Derivation
