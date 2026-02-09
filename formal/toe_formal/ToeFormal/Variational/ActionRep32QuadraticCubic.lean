/-
ToeFormal/Variational/ActionRep32QuadraticCubic.lean

Quadratic and cubic Rep32 action classes (structural-only).

Scope:
- Defines quadratic and cubic (grid-sum style) action functionals on FieldRep32.
- Provides pairing symmetry and left-linearity lemmas.
- Proves an exact finite-difference identity for the quadratic action
  (with explicit second-order remainder).
- Packages assumption-scoped discharge lemmas for the Rep32 finite-difference bridge.
-/

import Mathlib
import ToeFormal.Variational.ActionToFirstVariationBridgeRep32
import ToeFormal.Variational.PerturbationAlgebraRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false
open BigOperators
open scoped ComplexConjugate

/-! ### Pairing symmetry and left-linearity -/

theorem gridPairing_comm {nx ny : Nat} (x y : FieldGrid nx ny) :
    gridPairing x y = gridPairing y x := by
  classical
  unfold gridPairing
  refine Finset.sum_congr rfl ?_
  intro ij _
  ring

theorem pairingRep32'_comm (x y : FieldRep32) :
    pairingRep32' x y = pairingRep32' y x := by
  refine Quot.induction_on x ?_
  intro x
  refine Quot.induction_on y ?_
  intro y
  classical
  simp [pairingRep32', pairingContractRep, pairingRep32, RepQ32, gridPairing_comm]

theorem pairingRep32'_add_left (x y z : FieldRep32) :
    pairingRep32' (rep32Add x y) z = pairingRep32' x z + pairingRep32' y z := by
  calc
    pairingRep32' (rep32Add x y) z = pairingRep32' z (rep32Add x y) := by
      simp [pairingRep32'_comm]
    _ = pairingRep32' z x + pairingRep32' z y := by
      simpa using (pairingRep32'_add_right z x y)
    _ = pairingRep32' x z + pairingRep32' y z := by
      simp [pairingRep32'_comm]

theorem pairingRep32'_smul_left (x y : FieldRep32) (c : ℝ) :
    pairingRep32' (rep32Smul c x) y = c * pairingRep32' x y := by
  calc
    pairingRep32' (rep32Smul c x) y = pairingRep32' y (rep32Smul c x) := by
      simp [pairingRep32'_comm]
    _ = c * pairingRep32' y x := by
      simpa using (pairingRep32'_smul_right y x c)
    _ = c * pairingRep32' x y := by
      simp [pairingRep32'_comm]

/-! ### Quadratic action (grid sum of |ψ|^2) -/

/-- Quadratic action: grid sum of |ψ|^2. -/
def actionRep32Quadratic (ψ : FieldRep32) : ℝ :=
  pairingRep32' ψ ψ

/-- Quadratic representer (formal gradient): `2 ψ`. -/
def P_quad_rep32 (ψ : FieldRep32) : FieldRep32 :=
  rep32Smul 2 ψ

theorem differenceQuotientRep32_quadratic
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32)
    (ε : ℝ) (hε : ε ≠ 0) :
    differenceQuotientRep32 actionRep32Quadratic δ ψ ε =
      pairingRep32' (P_quad_rep32 ψ) (δ ψ) +
        ε * pairingRep32' (δ ψ) (δ ψ) := by
  set a : FieldRep32 := rep32Smul ε (δ ψ)
  have h_expand :
      pairingRep32' (rep32Add ψ a) (rep32Add ψ a) =
        pairingRep32' ψ ψ + pairingRep32' ψ a + pairingRep32' a ψ + pairingRep32' a a := by
    calc
      pairingRep32' (rep32Add ψ a) (rep32Add ψ a)
          = pairingRep32' ψ (rep32Add ψ a) + pairingRep32' a (rep32Add ψ a) := by
              simpa using (pairingRep32'_add_left ψ a (rep32Add ψ a))
      _ = (pairingRep32' ψ ψ + pairingRep32' ψ a) +
          (pairingRep32' a ψ + pairingRep32' a a) := by
              simp [pairingRep32'_add_right]
      _ = pairingRep32' ψ ψ + pairingRep32' ψ a + pairingRep32' a ψ + pairingRep32' a a := by
              ring
  have h_comm : pairingRep32' a ψ = pairingRep32' ψ a := by
    simpa using (pairingRep32'_comm a ψ)
  have hψa : pairingRep32' ψ a = ε * pairingRep32' ψ (δ ψ) := by
    simpa [a] using (pairingRep32'_smul_right ψ (δ ψ) ε)
  have haa : pairingRep32' a a = ε * (ε * pairingRep32' (δ ψ) (δ ψ)) := by
    calc
      pairingRep32' a a = pairingRep32' (rep32Smul ε (δ ψ)) (rep32Smul ε (δ ψ)) := by
        simp [a]
      _ = ε * pairingRep32' (δ ψ) (rep32Smul ε (δ ψ)) := by
        simpa using (pairingRep32'_smul_left (δ ψ) (rep32Smul ε (δ ψ)) ε)
      _ = ε * (ε * pairingRep32' (δ ψ) (δ ψ)) := by
        simp [pairingRep32'_smul_right]
  calc
    differenceQuotientRep32 actionRep32Quadratic δ ψ ε
        = ((pairingRep32' (rep32Add ψ a) (rep32Add ψ a)) - pairingRep32' ψ ψ) / ε := by
            rfl
    _ = ((pairingRep32' ψ ψ + pairingRep32' ψ a + pairingRep32' a ψ + pairingRep32' a a) -
          pairingRep32' ψ ψ) / ε := by
            simp [h_expand]
    _ = ((pairingRep32' ψ a + pairingRep32' a ψ + pairingRep32' a a)) / ε := by
            ring
    _ = ((2 * pairingRep32' ψ a + pairingRep32' a a)) / ε := by
            simp [h_comm, two_mul, add_assoc]
    _ = ((2 * (ε * pairingRep32' ψ (δ ψ)) + ε * (ε * pairingRep32' (δ ψ) (δ ψ)))) / ε := by
            simp [hψa, haa]
    _ = pairingRep32' (P_quad_rep32 ψ) (δ ψ) + ε * pairingRep32' (δ ψ) (δ ψ) := by
            field_simp [hε]
            simp [P_quad_rep32, pairingRep32'_smul_left]

/-- Assumption: all variations have zero self-pairing (kills the quadratic remainder). -/
def ActionRep32QuadraticNoSecondOrder : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    pairingRep32' (δ ψ) (δ ψ) = 0

theorem ActionRep32FiniteDifferenceRepresentsP_of_quadratic
    (hAction : actionRep32.action = actionRep32Quadratic)
    (hP : P_rep32 = P_quad_rep32)
    (hNo2 : ActionRep32QuadraticNoSecondOrder)
    (ε : ℝ) (hε : ε ≠ 0) :
    ActionRep32FiniteDifferenceRepresentsP ε hε := by
  intro δ ψ
  have hdiff :=
    differenceQuotientRep32_quadratic (δ := δ) (ψ := ψ) (ε := ε) hε
  have hno := hNo2 δ ψ
  calc
    formalFirstVariationRep32OpAt ε actionRep32.action δ ψ
        = differenceQuotientRep32 actionRep32.action δ ψ ε := by
            rfl
    _ = differenceQuotientRep32 actionRep32Quadratic δ ψ ε := by
            simp [hAction]
    _ = pairingRep32' (P_quad_rep32 ψ) (δ ψ) + ε * pairingRep32' (δ ψ) (δ ψ) := by
            simpa using hdiff
    _ = pairingRep32' (P_quad_rep32 ψ) (δ ψ) := by
            simp [hno]
    _ = pairingRep32' (P_rep32 ψ) (δ ψ) := by
            simp [hP]

/-! ### Cubic action (pointwise `g * |ψ|^2 * ψ`, lifted to Rep32) -/

/-- Pointwise cubic operator on Field2D. -/
def cubicField2D (g : ℂ) (ψ : Field2D) : Field2D :=
  fun x y t => g * ((Complex.normSq (ψ x y t)) : ℂ) * (ψ x y t)

/-- Real dot product on ℂ (pairing kernel). -/
def dotR (z w : ℂ) : ℝ :=
  z.re * w.re + z.im * w.im

theorem dotR_eq_re_mul_conj (z w : ℂ) : dotR z w = (z * conj w).re := by
  simp [dotR, Complex.mul_re, Complex.conj_re, Complex.conj_im, sub_eq_add_neg]

/-! Pointwise cubic cross terms (for explicit polynomial expansion). -/

def cubicCross1 (g : ℂ) (ψ η : Field2D) : Field2D :=
  fun x y t => g * ((Complex.normSq (ψ x y t)) : ℂ) * (η x y t)

def cubicCross2 (g : ℂ) (ψ η : Field2D) : Field2D :=
  fun x y t => g * ((2 * dotR (ψ x y t) (η x y t)) : ℂ) * (ψ x y t)

def cubicCross3 (g : ℂ) (ψ η : Field2D) : Field2D :=
  fun x y t => g * ((Complex.normSq (η x y t)) : ℂ) * (ψ x y t)

def cubicCross4 (g : ℂ) (ψ η : Field2D) : Field2D :=
  fun x y t => g * ((2 * dotR (ψ x y t) (η x y t)) : ℂ) * (η x y t)

theorem dotR_smul_right (c : ℝ) (z w : ℂ) : dotR z (c • w) = c * dotR z w := by
  simp [dotR, mul_add, mul_left_comm, mul_comm]

theorem dotR_mul_real_right (c : ℝ) (z w : ℂ) :
    dotR z ((c : ℂ) * w) = c * dotR z w := by
  simpa [smul_eq_mul] using (dotR_smul_right c z w)

theorem dotR_mul_real_right_comm (c : ℝ) (z w : ℂ) :
    dotR z (w * (c : ℂ)) = c * dotR z w := by
  simpa [mul_comm] using (dotR_mul_real_right c z w)

theorem normSq_smul_real (c : ℝ) (z : ℂ) :
    Complex.normSq (c • z) = c ^ 2 * Complex.normSq z := by
  -- use complex multiplication for real scalar
  simp [Complex.normSq_mul, Complex.normSq_ofReal, pow_two, mul_assoc, mul_comm]

theorem cubicCross1_smul_right (g : ℂ) (ψ η : Field2D) (c : ℝ) :
    cubicCross1 g ψ (c • η) = c • cubicCross1 g ψ η := by
  funext x y t
  simp [cubicCross1, mul_assoc, mul_left_comm, mul_comm]

theorem cubicCross2_smul_right (g : ℂ) (ψ η : Field2D) (c : ℝ) :
    cubicCross2 g ψ (c • η) = c • cubicCross2 g ψ η := by
  funext x y t
  simp [cubicCross2, dotR_mul_real_right_comm, mul_left_comm, mul_comm]

theorem cubicCross3_smul_right (g : ℂ) (ψ η : Field2D) (c : ℝ) :
    cubicCross3 g ψ (c • η) = (c ^ 2) • cubicCross3 g ψ η := by
  funext x y t
  simp [cubicCross3, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem cubicCross4_smul_right (g : ℂ) (ψ η : Field2D) (c : ℝ) :
    cubicCross4 g ψ (c • η) = (c ^ 2) • cubicCross4 g ψ η := by
  funext x y t
  simp [cubicCross4, dotR_mul_real_right_comm, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem cubicField2D_smul (g : ℂ) (ψ : Field2D) (c : ℝ) :
    cubicField2D g (c • ψ) = (c ^ 3) • cubicField2D g ψ := by
  funext x y t
  simp [cubicField2D, pow_succ, mul_assoc, mul_left_comm, mul_comm]

theorem cubicField2D_add (g : ℂ) (ψ η : Field2D) :
    cubicField2D g (ψ + η) =
      cubicField2D g ψ +
      cubicCross1 g ψ η +
      cubicCross2 g ψ η +
      cubicCross3 g ψ η +
      cubicCross4 g ψ η +
      cubicField2D g η := by
  funext x y t
  have hnorm :
      Complex.normSq (ψ x y t + η x y t) =
        Complex.normSq (ψ x y t) +
        Complex.normSq (η x y t) +
        2 * dotR (ψ x y t) (η x y t) := by
    simpa [dotR_eq_re_mul_conj] using
      (Complex.normSq_add (ψ x y t) (η x y t))
  simp [cubicField2D, cubicCross1, cubicCross2, cubicCross3, cubicCross4, hnorm,
    add_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_left_comm, mul_comm]

/-! Rep32 lift helpers for cubic cross terms. -/

def P_cubic_cross1_rep32 (g : ℂ) : FieldRep32 -> FieldRep32 -> FieldRep32 :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk _ (cubicCross1 g x y))
      (by
        intro y1 y2 hy
        apply Quot.sound
        funext i j
        have hy' := congrArg (fun f => f i j) hy
        simp [Rep32] at hy'
        simp [cubicCross1, Rep32, hy']))
    (by
      intro x1 x2 hx
      funext yq
      refine Quot.induction_on yq ?_
      intro y
      apply Quot.sound
      funext i j
      have hx' := congrArg (fun f => f i j) hx
      simp [Rep32] at hx'
      simp [cubicCross1, Rep32, hx'])

def P_cubic_cross2_rep32 (g : ℂ) : FieldRep32 -> FieldRep32 -> FieldRep32 :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk _ (cubicCross2 g x y))
      (by
        intro y1 y2 hy
        apply Quot.sound
        funext i j
        have hy' := congrArg (fun f => f i j) hy
        simp [Rep32] at hy'
        simp [cubicCross2, dotR, Rep32, hy']))
    (by
      intro x1 x2 hx
      funext yq
      refine Quot.induction_on yq ?_
      intro y
      apply Quot.sound
      funext i j
      have hx' := congrArg (fun f => f i j) hx
      simp [Rep32] at hx'
      simp [cubicCross2, dotR, Rep32, hx'])

def P_cubic_cross3_rep32 (g : ℂ) : FieldRep32 -> FieldRep32 -> FieldRep32 :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk _ (cubicCross3 g x y))
      (by
        intro y1 y2 hy
        apply Quot.sound
        funext i j
        have hy' := congrArg (fun f => f i j) hy
        simp [Rep32] at hy'
        simp [cubicCross3, Rep32, hy']))
    (by
      intro x1 x2 hx
      funext yq
      refine Quot.induction_on yq ?_
      intro y
      apply Quot.sound
      funext i j
      have hx' := congrArg (fun f => f i j) hx
      simp [Rep32] at hx'
      simp [cubicCross3, Rep32, hx'])

def P_cubic_cross4_rep32 (g : ℂ) : FieldRep32 -> FieldRep32 -> FieldRep32 :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk _ (cubicCross4 g x y))
      (by
        intro y1 y2 hy
        apply Quot.sound
        funext i j
        have hy' := congrArg (fun f => f i j) hy
        simp [Rep32] at hy'
        simp [cubicCross4, dotR, Rep32, hy']))
    (by
      intro x1 x2 hx
      funext yq
      refine Quot.induction_on yq ?_
      intro y
      apply Quot.sound
      funext i j
      have hx' := congrArg (fun f => f i j) hx
      simp [Rep32] at hx'
      simp [cubicCross4, dotR, Rep32, hx'])

/-- Rep32 lift of the pointwise cubic operator. -/
def P_cubic_rep32_def (g : ℂ) : FieldRep32 -> FieldRep32 :=
  Quot.lift (fun ψ => Quot.mk _ (cubicField2D g ψ))
    (by
      intro x y h
      apply Quot.sound
      funext i j
      have hxy := congrArg (fun f => f i j) h
      -- unfold Rep32 at the sample points
      simp [Rep32] at hxy
      -- use pointwise equality to rewrite the cubic term
      simp [cubicField2D, Rep32, hxy])

theorem P_cubic_cross1_rep32_smul_right
    (g : ℂ) (ψ η : FieldRep32) (c : ℝ) :
    P_cubic_cross1_rep32 g ψ (rep32Smul c η) =
      rep32Smul c (P_cubic_cross1_rep32 g ψ η) := by
  refine Quot.induction_on ψ ?_
  intro x
  refine Quot.induction_on η ?_
  intro y
  simp [P_cubic_cross1_rep32, rep32Smul_mk, cubicCross1_smul_right]

theorem P_cubic_cross2_rep32_smul_right
    (g : ℂ) (ψ η : FieldRep32) (c : ℝ) :
    P_cubic_cross2_rep32 g ψ (rep32Smul c η) =
      rep32Smul c (P_cubic_cross2_rep32 g ψ η) := by
  refine Quot.induction_on ψ ?_
  intro x
  refine Quot.induction_on η ?_
  intro y
  simp [P_cubic_cross2_rep32, rep32Smul_mk, cubicCross2_smul_right]

theorem P_cubic_cross3_rep32_smul_right
    (g : ℂ) (ψ η : FieldRep32) (c : ℝ) :
    P_cubic_cross3_rep32 g ψ (rep32Smul c η) =
      rep32Smul (c ^ 2) (P_cubic_cross3_rep32 g ψ η) := by
  refine Quot.induction_on ψ ?_
  intro x
  refine Quot.induction_on η ?_
  intro y
  simp [P_cubic_cross3_rep32, rep32Smul_mk, cubicCross3_smul_right]

theorem P_cubic_cross4_rep32_smul_right
    (g : ℂ) (ψ η : FieldRep32) (c : ℝ) :
    P_cubic_cross4_rep32 g ψ (rep32Smul c η) =
      rep32Smul (c ^ 2) (P_cubic_cross4_rep32 g ψ η) := by
  refine Quot.induction_on ψ ?_
  intro x
  refine Quot.induction_on η ?_
  intro y
  simp [P_cubic_cross4_rep32, rep32Smul_mk, cubicCross4_smul_right]

theorem P_cubic_rep32_def_smul
    (g : ℂ) (ψ : FieldRep32) (c : ℝ) :
    P_cubic_rep32_def g (rep32Smul c ψ) =
      rep32Smul (c ^ 3) (P_cubic_rep32_def g ψ) := by
  refine Quot.induction_on ψ ?_
  intro x
  simp [P_cubic_rep32_def, rep32Smul_mk, cubicField2D_smul]

theorem P_cubic_rep32_def_add
    (g : ℂ) (ψ a : FieldRep32) :
    P_cubic_rep32_def g (rep32Add ψ a) =
      rep32Add (P_cubic_rep32_def g ψ)
        (rep32Add (P_cubic_cross1_rep32 g ψ a)
          (rep32Add (P_cubic_cross2_rep32 g ψ a)
            (rep32Add (P_cubic_cross3_rep32 g ψ a)
              (rep32Add (P_cubic_cross4_rep32 g ψ a)
                (P_cubic_rep32_def g a))))) := by
  refine Quot.induction_on₂ ψ a ?_
  intro x y
  apply Quot.sound
  funext i j
  simp [cubicField2D_add, cubicCross1, cubicCross2, cubicCross3, cubicCross4, Rep32]
  ring

/-- Cubic action (quartic density): pairing with the cubic operator. -/
def actionRep32Cubic (g : ℂ) (ψ : FieldRep32) : ℝ :=
  pairingRep32' (P_cubic_rep32_def g ψ) ψ

theorem actionRep32Cubic_add_expand (g : ℂ) (ψ a : FieldRep32) :
    actionRep32Cubic g (rep32Add ψ a) =
      actionRep32Cubic g ψ +
      pairingRep32' (P_cubic_rep32_def g ψ) a +
      pairingRep32' (P_cubic_cross1_rep32 g ψ a) ψ +
      pairingRep32' (P_cubic_cross2_rep32 g ψ a) ψ +
      pairingRep32' (P_cubic_cross1_rep32 g ψ a) a +
      pairingRep32' (P_cubic_cross2_rep32 g ψ a) a +
      pairingRep32' (P_cubic_cross3_rep32 g ψ a) ψ +
      pairingRep32' (P_cubic_cross4_rep32 g ψ a) ψ +
      pairingRep32' (P_cubic_cross3_rep32 g ψ a) a +
      pairingRep32' (P_cubic_cross4_rep32 g ψ a) a +
      pairingRep32' (P_cubic_rep32_def g a) ψ +
      pairingRep32' (P_cubic_rep32_def g a) a := by
  unfold actionRep32Cubic
  calc
    pairingRep32' (P_cubic_rep32_def g (rep32Add ψ a)) (rep32Add ψ a)
        =
        pairingRep32'
          (rep32Add (P_cubic_rep32_def g ψ)
            (rep32Add (P_cubic_cross1_rep32 g ψ a)
              (rep32Add (P_cubic_cross2_rep32 g ψ a)
                (rep32Add (P_cubic_cross3_rep32 g ψ a)
                  (rep32Add (P_cubic_cross4_rep32 g ψ a)
                    (P_cubic_rep32_def g a))))))
          (rep32Add ψ a) := by
            simp [P_cubic_rep32_def_add]
    _ =
        pairingRep32' (P_cubic_rep32_def g ψ) ψ +
        pairingRep32' (P_cubic_rep32_def g ψ) a +
        pairingRep32' (P_cubic_cross1_rep32 g ψ a) ψ +
        pairingRep32' (P_cubic_cross2_rep32 g ψ a) ψ +
        pairingRep32' (P_cubic_cross1_rep32 g ψ a) a +
        pairingRep32' (P_cubic_cross2_rep32 g ψ a) a +
        pairingRep32' (P_cubic_cross3_rep32 g ψ a) ψ +
        pairingRep32' (P_cubic_cross4_rep32 g ψ a) ψ +
        pairingRep32' (P_cubic_cross3_rep32 g ψ a) a +
        pairingRep32' (P_cubic_cross4_rep32 g ψ a) a +
        pairingRep32' (P_cubic_rep32_def g a) ψ +
        pairingRep32' (P_cubic_rep32_def g a) a := by
          simp [pairingRep32'_add_left, pairingRep32'_add_right, add_assoc, add_left_comm, add_comm]
/-! ### Explicit polynomial expansion for the cubic action -/

def cubicLinearTerm
    (g : ℂ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  pairingRep32' (P_cubic_rep32_def g ψ) (δ ψ) +
  pairingRep32' (P_cubic_cross1_rep32 g ψ (δ ψ)) ψ +
  pairingRep32' (P_cubic_cross2_rep32 g ψ (δ ψ)) ψ

def cubicRemainder₂
    (g : ℂ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  pairingRep32' (P_cubic_cross1_rep32 g ψ (δ ψ)) (δ ψ) +
  pairingRep32' (P_cubic_cross2_rep32 g ψ (δ ψ)) (δ ψ) +
  pairingRep32' (P_cubic_cross3_rep32 g ψ (δ ψ)) ψ +
  pairingRep32' (P_cubic_cross4_rep32 g ψ (δ ψ)) ψ

def cubicRemainder₃
    (g : ℂ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  pairingRep32' (P_cubic_cross3_rep32 g ψ (δ ψ)) (δ ψ) +
  pairingRep32' (P_cubic_cross4_rep32 g ψ (δ ψ)) (δ ψ) +
  pairingRep32' (P_cubic_rep32_def g (δ ψ)) ψ

def cubicRemainder₄
    (g : ℂ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  pairingRep32' (P_cubic_rep32_def g (δ ψ)) (δ ψ)

def ActionRep32CubicLinearMatchesP (g : ℂ) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    cubicLinearTerm g δ ψ = pairingRep32' (P_cubic_rep32_def g ψ) (δ ψ)

theorem differenceQuotientRep32_cubic_expand
    (g : ℂ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32)
    (ε : ℝ) (hε : ε ≠ 0) :
    differenceQuotientRep32 (actionRep32Cubic g) δ ψ ε =
      cubicLinearTerm g δ ψ +
      ε * cubicRemainder₂ g δ ψ +
      ε^2 * cubicRemainder₃ g δ ψ +
      ε^3 * cubicRemainder₄ g δ ψ := by
  classical
  set a : FieldRep32 := rep32Smul ε (δ ψ)
  have hexp := actionRep32Cubic_add_expand (g := g) (ψ := ψ) (a := a)
  calc
    differenceQuotientRep32 (actionRep32Cubic g) δ ψ ε
        = ((actionRep32Cubic g) (rep32Add ψ a) - (actionRep32Cubic g) ψ) / ε := by
            rfl
    _ = ((actionRep32Cubic g ψ +
            pairingRep32' (P_cubic_rep32_def g ψ) a +
            pairingRep32' (P_cubic_cross1_rep32 g ψ a) ψ +
            pairingRep32' (P_cubic_cross2_rep32 g ψ a) ψ +
            pairingRep32' (P_cubic_cross1_rep32 g ψ a) a +
            pairingRep32' (P_cubic_cross2_rep32 g ψ a) a +
            pairingRep32' (P_cubic_cross3_rep32 g ψ a) ψ +
            pairingRep32' (P_cubic_cross4_rep32 g ψ a) ψ +
            pairingRep32' (P_cubic_cross3_rep32 g ψ a) a +
            pairingRep32' (P_cubic_cross4_rep32 g ψ a) a +
            pairingRep32' (P_cubic_rep32_def g a) ψ +
            pairingRep32' (P_cubic_rep32_def g a) a) -
          actionRep32Cubic g ψ) / ε := by
            simp [hexp]
    _ =
        (pairingRep32' (P_cubic_rep32_def g ψ) a +
          pairingRep32' (P_cubic_cross1_rep32 g ψ a) ψ +
          pairingRep32' (P_cubic_cross2_rep32 g ψ a) ψ +
          pairingRep32' (P_cubic_cross1_rep32 g ψ a) a +
          pairingRep32' (P_cubic_cross2_rep32 g ψ a) a +
          pairingRep32' (P_cubic_cross3_rep32 g ψ a) ψ +
          pairingRep32' (P_cubic_cross4_rep32 g ψ a) ψ +
          pairingRep32' (P_cubic_cross3_rep32 g ψ a) a +
          pairingRep32' (P_cubic_cross4_rep32 g ψ a) a +
          pairingRep32' (P_cubic_rep32_def g a) ψ +
          pairingRep32' (P_cubic_rep32_def g a) a) / ε := by
            ring
    _ = cubicLinearTerm g δ ψ +
        ε * cubicRemainder₂ g δ ψ +
        ε^2 * cubicRemainder₃ g δ ψ +
        ε^3 * cubicRemainder₄ g δ ψ := by
          -- Substitute a = ε δψ and pull out powers of ε.
          field_simp [hε]
          simp [
            cubicLinearTerm, cubicRemainder₂, cubicRemainder₃, cubicRemainder₄,
            a,
            P_cubic_cross1_rep32_smul_right, P_cubic_cross2_rep32_smul_right,
            P_cubic_cross3_rep32_smul_right, P_cubic_cross4_rep32_smul_right,
            P_cubic_rep32_def_smul, pairingRep32'_smul_right, pairingRep32'_smul_left,
            pow_succ, mul_assoc, mul_comm, add_assoc, add_comm
          ]
          ring

def ActionRep32CubicNoSecondOrder (g : ℂ) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    cubicRemainder₂ g δ ψ = 0

def ActionRep32CubicNoThirdOrder (g : ℂ) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    cubicRemainder₃ g δ ψ = 0

def ActionRep32CubicNoFourthOrder (g : ℂ) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    cubicRemainder₄ g δ ψ = 0

theorem ActionRep32FiniteDifferenceRepresentsP_of_cubic
    (g : ℂ)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (h1 : ActionRep32CubicLinearMatchesP g)
    (h2 : ActionRep32CubicNoSecondOrder g)
    (h3 : ActionRep32CubicNoThirdOrder g)
    (h4 : ActionRep32CubicNoFourthOrder g)
    (ε : ℝ) (hε : ε ≠ 0) :
    ActionRep32FiniteDifferenceRepresentsP ε hε := by
  intro δ ψ
  have hexp := differenceQuotientRep32_cubic_expand
    (g := g) (δ := δ) (ψ := ψ) (ε := ε) hε
  have h1' := h1 δ ψ
  have h2' := h2 δ ψ
  have h3' := h3 δ ψ
  have h4' := h4 δ ψ
  calc
    formalFirstVariationRep32OpAt ε actionRep32.action δ ψ
        = differenceQuotientRep32 actionRep32.action δ ψ ε := by
            rfl
    _ = differenceQuotientRep32 (actionRep32Cubic g) δ ψ ε := by
            simp [hAction]
    _ = cubicLinearTerm g δ ψ +
        ε * cubicRemainder₂ g δ ψ +
        ε^2 * cubicRemainder₃ g δ ψ +
        ε^3 * cubicRemainder₄ g δ ψ := by
            simpa using hexp
    _ = pairingRep32' (P_cubic_rep32_def g ψ) (δ ψ) := by
            simp [h1', h2', h3', h4']
    _ = pairingRep32' (P_rep32 ψ) (δ ψ) := by
            simp [hP]

end

end Variational
end ToeFormal
