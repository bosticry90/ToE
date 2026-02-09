import Mathlib
import ToeFormal.UCFF.SecondOrderTimeDomain
import ToeFormal.Derivation.Parents.P2_Wave_EFT

namespace ToeFormal
namespace Derivation
namespace Bridges

open ToeFormal
open ToeFormal.UCFF
open ToeFormal.Derivation.Parents

noncomputable section
set_option autoImplicit false

-- Status: Spec-backed (axiom placeholders present)

/-
B2: P2 (wave-type parent) → UCFF Second-Order Time Domain lock.

Goals in this bridge file:
- Provide an explicit coefficient map from UCFF parameters (g, lam, beta) to Parent P2 coefficients.
- Bridge at the ω²(k) symbol/polynomial level (linearized dispersion) using a definitional lemma.
- Provide a residual-form mapping P2 waveResidual ↔ UCFF secondOrderTimeDomainResidual.

Operator alignment is currently spec-backed (axiom placeholders) because Parent P2 and UCFF
each declare opaque derivative operators.
-/

/-! ### (1) Coefficient matching

UCFF residual (locked shape):
  Dtt φ + (1/2) Dxx φ - lam Dxxxx φ - beta Dxxxxxx φ + cubicDensity(g) = 0

Parent P2 residual (P2_Wave_EFT):
  Dtt φ + c2 Dxx φ + c4 Dxxxx φ + c6 Dxxxxxx φ + cubicDensity(g3) = 0

Intended mapping:
  g3 := g
  c2 := 1/2
  c4 := -lam
  c6 := -beta
-/

/-- Coefficient map from UCFF parameters to parent P2 coefficients. -/
def coeffMap (g lam beta : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (g, (1 / 2 : ℝ), -lam, -beta)  -- (g3, c2, c4, c6)

/-- Convenience: package the mapped linear coefficients into `P2Params` (c2,c4,c6);
cubic coefficient ge3 remains an explicit argument to waveResidual/SatisfiesWaveP2. -/
def toP2Params (g lam beta : ℝ) : P2Params :=
  let (_g3, c2, c4, c6) := coeffMap g lam beta
  P2Params.mk c2 c4 c6

/-! ### (2) Symbol-level bridge (ω² polynomial)

Parent P2 provides a linearized dispersion polynomial `ωsq_linear_P2`.
For the UCFF second-order time-domain lock, we treat the mapped Parent polynomial
as the symbol definition (README TODO #3).
-/

/-- ω²(k) symbol associated to the UCFF time-domain lock,
    defined via the mapped Parent polynomial. -/
def omegaSq_symbol_UCFF_TimeDomain (g lam beta k : ℝ) : ℝ :=
  ωsq_linear_P2 (toP2Params g lam beta) k

/-- The symbol-level bridge is definitional: UCFF ω² symbol is Parent P2 ω²
    under the coefficient map. -/
theorem omegaSq_symbol_bridge (g lam beta k : ℝ) :
    omegaSq_symbol_UCFF_TimeDomain g lam beta k =
      ωsq_linear_P2 (toP2Params g lam beta) k := by
  rfl

/-! ### (3) Operator alignment assumptions (spec)

Until Parent and UCFF share a single operator layer, we keep explicit *_spec axioms
stating that the intended derivative operators and cubic term agree.
-/

axiom Dtt_agrees_spec :
  (ToeFormal.Derivation.Parents.Dtt : FieldC → FieldC) =
    (ToeFormal.UCFF.Dtt : UCFF.Field → UCFF.Field)

axiom Dxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxx : FieldC → FieldC) =
    (ToeFormal.UCFF.Dxx : UCFF.Field → UCFF.Field)

axiom Dxxxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxxxx : FieldC → FieldC) =
    (ToeFormal.UCFF.Dxxxx : UCFF.Field → UCFF.Field)

axiom Dxxxxxx_agrees_spec :
  (ToeFormal.Derivation.Parents.Dxxxxxx : FieldC → FieldC) =
    (ToeFormal.UCFF.Dxxxxxx : UCFF.Field → UCFF.Field)

axiom cubicDensity_agrees_spec (g : ℝ) (phi : ToeFormal.UCFF.Field) :
  ToeFormal.Derivation.Parents.cubicDensity g (phi : FieldC) =
    ToeFormal.UCFF.cubicDensity g phi

/-! ### (4) Residual-form bridge lemma

Once the operator alignments are discharged (by sharing operators or definitional aliases),
this proof should reduce to `simp`/`rfl`.
-/

theorem parentResidual_matches_ucffResidual
    (g lam beta : ℝ) (phi : UCFF.Field) (t x : ℝ) :
    let (g3, c2, c4, c6) := coeffMap g lam beta
    waveResidual c2 c4 c6 g3 (phi : FieldC) t x
      =
    UCFF.secondOrderTimeDomainResidual g lam beta phi t x := by
  dsimp [
    waveResidual,
    UCFF.secondOrderTimeDomainResidual,
    UCFF.secondOrderTimeDomainResidual_expand
  ]
  have hDtt :
      (ToeFormal.Derivation.Parents.Dtt (phi : FieldC) t x)
        = (ToeFormal.UCFF.Dtt phi) t x := by
    simpa using congrArg (fun D => D (phi : FieldC) t x) Dtt_agrees_spec
  have hDxx :
      (ToeFormal.Derivation.Parents.Dxx (phi : FieldC) t x)
        = (ToeFormal.UCFF.Dxx phi) t x := by
    simpa using congrArg (fun D => D (phi : FieldC) t x) Dxx_agrees_spec
  have hDxxxx :
      (ToeFormal.Derivation.Parents.Dxxxx (phi : FieldC) t x)
        = (ToeFormal.UCFF.Dxxxx phi) t x := by
    simpa using congrArg (fun D => D (phi : FieldC) t x) Dxxxx_agrees_spec
  have hDxxxxxx :
      (ToeFormal.Derivation.Parents.Dxxxxxx (phi : FieldC) t x)
        = (ToeFormal.UCFF.Dxxxxxx phi) t x := by
    simpa using congrArg (fun D => D (phi : FieldC) t x) Dxxxxxx_agrees_spec
  have hcubic :
      ToeFormal.Derivation.Parents.cubicDensity (coeffMap g lam beta).1 (phi : FieldC) t x =
        ToeFormal.UCFF.cubicDensity (coeffMap g lam beta).1 phi t x := by
    simpa using congrArg (fun f => f t x)
      (cubicDensity_agrees_spec (coeffMap g lam beta).1 phi)
  rw [hDtt, hDxx, hDxxxx, hDxxxxxx, hcubic]
  dsimp [coeffMap]
  simp [neg_mul, sub_eq_add_neg]

/-! ### (5) Bridge theorem

If the parent P2 residual holds with mapped coefficients, then the UCFF time-domain
residual holds.
-/

theorem B2_P2_to_UCFF_SecondOrderTimeDomain
    (g lam beta : ℝ) (phi : UCFF.Field) :
    let (g3, c2, c4, c6) := coeffMap g lam beta
    SatisfiesWaveP2 c2 c4 c6 g3 (phi : FieldC)
      →
    UCFF.SatisfiesSecondOrderTimeDomain g lam beta phi := by
  intro hP2 t x
  dsimp [SatisfiesWaveP2] at hP2
  have h0 :
      (let (g3, c2, c4, c6) := coeffMap g lam beta
       waveResidual c2 c4 c6 g3 (phi : FieldC) t x) = 0 := by
    exact hP2 t x
  have eq := parentResidual_matches_ucffResidual g lam beta phi t x
  have eq' :
      (let (g3, c2, c4, c6) := coeffMap g lam beta
       waveResidual c2 c4 c6 g3 (phi : FieldC) t x)
        = UCFF.secondOrderTimeDomainResidual g lam beta phi t x := by
    simpa using eq
  -- Rewrite the parent residual into the UCFF residual.
  have h0' : UCFF.secondOrderTimeDomainResidual g lam beta phi t x = 0 := by
    simpa [eq'] using h0
  exact h0'

end
end Bridges
end Derivation
end ToeFormal
