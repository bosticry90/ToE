/-
ToeFormal/Variational/PerturbationAlgebraRep32.lean

Perturbation algebra lemmas for the Rep32 finite-difference lane (structural-only).

Scope:
- Proves basic algebraic laws for rep32Zero/rep32Add/rep32Smul on FieldRep32.
- Derives perturbation identities (zeroVar, addVar/smulVar unfold + compatibility).
- Provides non-analytic finite-difference bookkeeping lemmas.
-/

import Mathlib
import ToeFormal.Variational.ActionToFirstVariationBridgeRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-! ### Basic quotient arithmetic laws -/

theorem rep32Add_mk (x y : Field2D) :
    rep32Add (Quot.mk _ x) (Quot.mk _ y) = Quot.mk _ (x + y) := by
  rfl

theorem rep32Smul_mk (c : ℝ) (x : Field2D) :
    rep32Smul c (Quot.mk _ x) = Quot.mk _ (c • x) := by
  rfl

theorem rep32Add_zero_left (q : FieldRep32) : rep32Add rep32Zero q = q := by
  refine Quot.induction_on q ?_
  intro x
  apply Quot.sound
  funext i j
  simp [Rep32, rep32ZeroField]

theorem rep32Add_zero_right (q : FieldRep32) : rep32Add q rep32Zero = q := by
  refine Quot.induction_on q ?_
  intro x
  apply Quot.sound
  funext i j
  simp [Rep32, rep32ZeroField]

theorem rep32Smul_zero (c : ℝ) : rep32Smul c rep32Zero = rep32Zero := by
  change rep32Smul c (Quot.mk _ rep32ZeroField) = Quot.mk _ rep32ZeroField
  apply Quot.sound
  funext i j
  simp [Rep32, rep32ZeroField]

theorem rep32Smul_one (q : FieldRep32) : rep32Smul (1 : ℝ) q = q := by
  refine Quot.induction_on q ?_
  intro x
  apply Quot.sound
  funext i j
  simp [Rep32]

theorem rep32Smul_smul (a b : ℝ) (q : FieldRep32) :
    rep32Smul a (rep32Smul b q) = rep32Smul (a * b) q := by
  refine Quot.induction_on q ?_
  intro x
  apply Quot.sound
  funext i j
  simp [Rep32, mul_assoc]

theorem rep32Smul_add (c : ℝ) (q1 q2 : FieldRep32) :
    rep32Smul c (rep32Add q1 q2) =
      rep32Add (rep32Smul c q1) (rep32Smul c q2) := by
  refine Quot.induction_on₂ q1 q2 ?_
  intro x y
  apply Quot.sound
  funext i j
  simp [Rep32, smul_add]

theorem rep32Add_assoc (q1 q2 q3 : FieldRep32) :
    rep32Add (rep32Add q1 q2) q3 = rep32Add q1 (rep32Add q2 q3) := by
  refine Quot.induction_on q1 ?_
  intro x
  refine Quot.induction_on q2 ?_
  intro y
  refine Quot.induction_on q3 ?_
  intro z
  apply Quot.sound
  funext i j
  simp [Rep32, add_assoc]

theorem rep32Add_comm (q1 q2 : FieldRep32) :
    rep32Add q1 q2 = rep32Add q2 q1 := by
  refine Quot.induction_on₂ q1 q2 ?_
  intro x y
  apply Quot.sound
  funext i j
  simp [Rep32, add_comm]

/-! ### Perturbation identities -/

theorem perturbRep32_unfold (ψ : FieldRep32) (δ : FieldRep32 -> FieldRep32) (ε : ℝ) :
    perturbRep32 ψ δ ε = rep32Add ψ (rep32Smul ε (δ ψ)) := by
  rfl

theorem perturbRep32_zeroVar (ψ : FieldRep32) (ε : ℝ) :
    perturbRep32 ψ formalFirstVariationRep32.zeroVar ε = ψ := by
  simp [perturbRep32, formalFirstVariationRep32, formalFirstVariationRep32At,
    formalFirstVariationRep32ZeroVar, rep32Add_zero_right, rep32Smul_zero]

theorem perturbRep32_addVar (ψ : FieldRep32)
    (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ε : ℝ) :
    perturbRep32 ψ (formalFirstVariationRep32.addVar δ₁ δ₂) ε =
      rep32Add ψ (rep32Smul ε (rep32Add (δ₁ ψ) (δ₂ ψ))) := by
  simp [perturbRep32, formalFirstVariationRep32, formalFirstVariationRep32At,
    formalFirstVariationRep32AddVar]

theorem perturbRep32_smulVar (ψ : FieldRep32)
    (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ε : ℝ) :
    perturbRep32 ψ (formalFirstVariationRep32.smulVar c δ) ε =
      rep32Add ψ (rep32Smul ε (rep32Smul c (δ ψ))) := by
  simp [perturbRep32, formalFirstVariationRep32, formalFirstVariationRep32At,
    formalFirstVariationRep32SmulVar]

/-! ### Finite-difference bookkeeping (no analytic limits) -/

theorem differenceQuotientRep32_const (ε c : ℝ)
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    differenceQuotientRep32 (fun _ => c) δ ψ ε = 0 := by
  simp [differenceQuotientRep32]

theorem formalFirstVariationRep32OpAt_const (ε c : ℝ)
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32OpAt ε (fun _ => c) δ ψ = 0 := by
  simp [formalFirstVariationRep32OpAt, differenceQuotientRep32]

theorem formalFirstVariationRep32Op_const (c : ℝ)
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32Op (fun _ => c) δ ψ = 0 := by
  simp [formalFirstVariationRep32Op, formalFirstVariationRep32OpAt,
    differenceQuotientRep32, rep32Step]

/-! ### Pairing linearity in the second slot (Rep32 quotient) -/

theorem pairingRep32'_add_right (x y z : FieldRep32) :
    pairingRep32' x (rep32Add y z) =
      pairingRep32' x y + pairingRep32' x z := by
  refine Quot.induction_on x ?_
  intro x
  refine Quot.induction_on y ?_
  intro y
  refine Quot.induction_on z ?_
  intro z
  classical
  -- unfold through the quotient pairing to the grid pairing
  simp [pairingRep32', pairingContractRep, pairingRep32, RepQ32, rep32Add_mk, Rep32_add,
    gridPairing, Finset.sum_add_distrib, Complex.add_re, Complex.add_im, mul_add,
    add_assoc, add_left_comm]

theorem pairingRep32'_smul_right (x y : FieldRep32) (c : ℝ) :
    pairingRep32' x (rep32Smul c y) = c * pairingRep32' x y := by
  refine Quot.induction_on x ?_
  intro x
  refine Quot.induction_on y ?_
  intro y
  classical
  simp [pairingRep32', pairingContractRep, pairingRep32, RepQ32, rep32Smul_mk, Rep32_smul,
    gridPairing, Complex.mul_re, Complex.mul_im, Finset.mul_sum, mul_add,
    mul_left_comm, add_comm]

/-! ### Linear action class (finite-difference exact) -/

def actionRep32Linear (P0 : FieldRep32) : FieldRep32 -> ℝ :=
  fun ψ => pairingRep32' P0 ψ

theorem differenceQuotientRep32_linear
    (P0 : FieldRep32) (δ : FieldRep32 -> FieldRep32)
    (ψ : FieldRep32) (ε : ℝ) (hε : ε ≠ 0) :
    differenceQuotientRep32 (actionRep32Linear P0) δ ψ ε =
      pairingRep32' P0 (δ ψ) := by
  have hlin :
      pairingRep32' P0 (rep32Smul ε (δ ψ)) =
        ε * pairingRep32' P0 (δ ψ) := by
    simpa using (pairingRep32'_smul_right P0 (δ ψ) ε)
  calc
    differenceQuotientRep32 (actionRep32Linear P0) δ ψ ε
        = ((actionRep32Linear P0) (perturbRep32 ψ δ ε) -
            (actionRep32Linear P0) ψ) / ε := by
              rfl
    _ = (pairingRep32' P0 (rep32Add ψ (rep32Smul ε (δ ψ))) -
          pairingRep32' P0 ψ) / ε := by
          rfl
    _ = (pairingRep32' P0 ψ + pairingRep32' P0 (rep32Smul ε (δ ψ)) -
          pairingRep32' P0 ψ) / ε := by
          simp [pairingRep32'_add_right]
    _ = (pairingRep32' P0 (rep32Smul ε (δ ψ))) / ε := by
          ring
    _ = (ε * pairingRep32' P0 (δ ψ)) / ε := by
          simp [hlin]
    _ = pairingRep32' P0 (δ ψ) := by
          field_simp [hε]

theorem ActionRep32FiniteDifferenceRepresentsP_of_linear
    (P0 : FieldRep32)
    (hAction : actionRep32.action = actionRep32Linear P0)
    (hP : ∀ ψ : FieldRep32, P_rep32 ψ = P0)
    (ε : ℝ) (hε : ε ≠ 0) :
    ActionRep32FiniteDifferenceRepresentsP ε hε := by
  intro δ ψ
  have hdiff :=
    differenceQuotientRep32_linear (P0 := P0) (δ := δ) (ψ := ψ) (ε := ε) hε
  simpa [formalFirstVariationRep32OpAt, hAction, actionRep32Linear, hP] using hdiff

end

end Variational
end ToeFormal
