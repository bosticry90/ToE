/-
ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean

Rep32 action-to-first-variation bridge boundary (structural-only).

Scope:
- Declares a formal "first variation" operator for Rep32 actions.
- Specifies a concrete finite-difference operator on the Rep32 quotient
  (no analysis imports; discrete step only).
- States the boundary condition equating `firstVariationRep32` to that formal operator.
- Keeps linearity laws as explicit axioms (analytic lane; not yet discharged).
- Does not provide analytic derivations.
-/

import Mathlib
import ToeFormal.Variational.ActionRep32Def
import ToeFormal.Variational.FirstVariationDeclaredRep32
import ToeFormal.Variational.FirstVariationRep32Def

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-!
Rep32 arithmetic on the quotient (lifted from Field2D).

We keep this minimal and explicit so the finite-difference operator is fully
specified while still avoiding analytic imports.
-/

/-- Canonical zero representative on Field2D. -/
def rep32ZeroField : Field2D := fun _ _ _ => 0

/-- Zero element on the Rep32 quotient (by representative). -/
def rep32Zero : FieldRep32 := Quot.mk _ rep32ZeroField

theorem Rep32_add (x y : Field2D) : Rep32 (x + y) = Rep32 x + Rep32 y := by
  funext i j
  simp [Rep32]

theorem Rep32_smul (c : ℝ) (x : Field2D) : Rep32 (c • x) = c • Rep32 x := by
  funext i j
  simp [Rep32]

theorem RepEq32_add {x x' y y' : Field2D} (hx : RepEq32 x x') (hy : RepEq32 y y') :
    RepEq32 (x + y) (x' + y') := by
  calc
    Rep32 (x + y) = Rep32 x + Rep32 y := Rep32_add x y
    _ = Rep32 x' + Rep32 y' := by rw [hx, hy]
    _ = Rep32 (x' + y') := (Rep32_add x' y').symm

theorem RepEq32_smul {x x' : Field2D} (c : ℝ) (hx : RepEq32 x x') :
    RepEq32 (c • x) (c • x') := by
  calc
    Rep32 (c • x) = c • Rep32 x := Rep32_smul c x
    _ = c • Rep32 x' := by rw [hx]
    _ = Rep32 (c • x') := (Rep32_smul c x').symm

/-- Addition on the Rep32 quotient (well-defined by Rep32 linearity). -/
def rep32Add : FieldRep32 -> FieldRep32 -> FieldRep32 :=
  Quot.lift
    (fun x =>
      Quot.lift (fun y => Quot.mk _ (x + y))
        (by
          intro y1 y2 hy
          apply Quot.sound
          have hx : RepEq32 x x := rfl
          exact RepEq32_add hx hy))
    (by
      intro x1 x2 hx
      funext yq
      refine Quot.induction_on yq ?_
      intro y
      apply Quot.sound
      have hy : RepEq32 y y := rfl
      exact RepEq32_add hx hy)

/-- Scalar multiplication on the Rep32 quotient (well-defined by Rep32 linearity). -/
def rep32Smul (c : ℝ) : FieldRep32 -> FieldRep32 :=
  Quot.lift (fun x => Quot.mk _ (c • x))
    (by
      intro x1 x2 hx
      apply Quot.sound
      exact RepEq32_smul (c := c) hx)

/-!
Finite-difference operator (discrete step, no analysis).
-/

/-- Perturbation of a Rep32 field by a variation at step `ε`. -/
def perturbRep32 (ψ : FieldRep32) (δ : FieldRep32 -> FieldRep32) (ε : ℝ) : FieldRep32 :=
  rep32Add ψ (rep32Smul ε (δ ψ))

/-- Fixed finite-difference step for the formal operator. -/
def rep32Step : ℝ := 1

/-- Guard: fixed step is nonzero (discrete surrogate; analytic limit out-of-scope). -/
theorem rep32Step_ne_zero : rep32Step ≠ 0 := by
  simp [rep32Step]

/-- Finite-difference quotient for an action on the Rep32 quotient. -/
def differenceQuotientRep32
    (A : FieldRep32 -> ℝ) (δ : FieldRep32 -> FieldRep32)
    (ψ : FieldRep32) (ε : ℝ) : ℝ :=
  (A (perturbRep32 ψ δ ε) - A ψ) / ε

-- Formal (non-analytic) first-variation operator for Rep32 actions.
-- Bundles minimal algebraic laws without adopting analysis.
structure FormalFirstVariationRep32 where
  op : (FieldRep32 -> ℝ) -> (FieldRep32 -> FieldRep32) -> FieldRep32 -> ℝ
  zeroVar : FieldRep32 -> FieldRep32
  addVar :
    (FieldRep32 -> FieldRep32) -> (FieldRep32 -> FieldRep32) -> FieldRep32 -> FieldRep32
  smulVar : ℝ -> (FieldRep32 -> FieldRep32) -> FieldRep32 -> FieldRep32
  zero_variation :
    ∀ (A : FieldRep32 -> ℝ) (ψ : FieldRep32),
      op A zeroVar ψ = 0
  add_variation :
    ∀ (A : FieldRep32 -> ℝ) (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      op A (addVar δ₁ δ₂) ψ = op A δ₁ ψ + op A δ₂ ψ
  smul_variation :
    ∀ (A : FieldRep32 -> ℝ) (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      op A (smulVar c δ) ψ = c * op A δ ψ
  zero_action :
    ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      op (fun _ => (0 : ℝ)) δ ψ = 0

/-- Explicit finite-difference operator at the fixed step. -/
def formalFirstVariationRep32OpAt (ε : ℝ)
    (A : FieldRep32 -> ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  differenceQuotientRep32 A δ ψ ε

/-- Explicit finite-difference operator at the fixed step. -/
def formalFirstVariationRep32Op
    (A : FieldRep32 -> ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : ℝ :=
  formalFirstVariationRep32OpAt rep32Step A δ ψ

/-- Formal zero variation (constant zero field). -/
def formalFirstVariationRep32ZeroVar : FieldRep32 -> FieldRep32 :=
  fun _ => rep32Zero

/-- Formal variation addition (pointwise on the quotient). -/
def formalFirstVariationRep32AddVar
    (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : FieldRep32 :=
  rep32Add (δ₁ ψ) (δ₂ ψ)

/-- Formal variation scalar multiplication (pointwise on the quotient). -/
def formalFirstVariationRep32SmulVar
    (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) : FieldRep32 :=
  rep32Smul c (δ ψ)

/-- Linearity of the finite-difference operator (analytic lane; explicit axiom). -/
axiom formalFirstVariationRep32_zero_variation_at :
  ∀ (ε : ℝ) (A : FieldRep32 -> ℝ) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε A formalFirstVariationRep32ZeroVar ψ = 0

/-- Linearity of the finite-difference operator (analytic lane; explicit axiom). -/
axiom formalFirstVariationRep32_add_variation_at :
  ∀ (ε : ℝ) (A : FieldRep32 -> ℝ) (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε A (formalFirstVariationRep32AddVar δ₁ δ₂) ψ =
      formalFirstVariationRep32OpAt ε A δ₁ ψ + formalFirstVariationRep32OpAt ε A δ₂ ψ

/-- Linearity of the finite-difference operator (analytic lane; explicit axiom). -/
axiom formalFirstVariationRep32_smul_variation_at :
  ∀ (ε : ℝ) (A : FieldRep32 -> ℝ) (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε A (formalFirstVariationRep32SmulVar c δ) ψ =
      c * formalFirstVariationRep32OpAt ε A δ ψ

theorem formalFirstVariationRep32_zero_variation
    (A : FieldRep32 -> ℝ) (ψ : FieldRep32) :
    formalFirstVariationRep32Op A formalFirstVariationRep32ZeroVar ψ = 0 := by
  simpa [formalFirstVariationRep32Op] using
    (formalFirstVariationRep32_zero_variation_at rep32Step A ψ)

theorem formalFirstVariationRep32_add_variation
    (A : FieldRep32 -> ℝ) (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32Op A (formalFirstVariationRep32AddVar δ₁ δ₂) ψ =
      formalFirstVariationRep32Op A δ₁ ψ + formalFirstVariationRep32Op A δ₂ ψ := by
  simpa [formalFirstVariationRep32Op] using
    (formalFirstVariationRep32_add_variation_at rep32Step A δ₁ δ₂ ψ)

theorem formalFirstVariationRep32_smul_variation
    (A : FieldRep32 -> ℝ) (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32Op A (formalFirstVariationRep32SmulVar c δ) ψ =
      c * formalFirstVariationRep32Op A δ ψ := by
  simpa [formalFirstVariationRep32Op] using
    (formalFirstVariationRep32_smul_variation_at rep32Step A c δ ψ)

theorem formalFirstVariationRep32_zero_action_at
    (ε : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32OpAt ε (fun _ => (0 : ℝ)) δ ψ = 0 := by
  simp [formalFirstVariationRep32OpAt, differenceQuotientRep32]

theorem formalFirstVariationRep32_zero_action
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    formalFirstVariationRep32Op (fun _ => (0 : ℝ)) δ ψ = 0 := by
  simp [formalFirstVariationRep32Op, formalFirstVariationRep32_zero_action_at]

/-- Declared formal first-variation operator bundle (finite-difference form, parameterized). -/
def formalFirstVariationRep32At (ε : ℝ) (_hε : ε ≠ 0) : FormalFirstVariationRep32 :=
  { op := formalFirstVariationRep32OpAt ε
    zeroVar := formalFirstVariationRep32ZeroVar
    addVar := formalFirstVariationRep32AddVar
    smulVar := formalFirstVariationRep32SmulVar
    zero_variation := formalFirstVariationRep32_zero_variation_at ε
    add_variation := formalFirstVariationRep32_add_variation_at ε
    smul_variation := formalFirstVariationRep32_smul_variation_at ε
    zero_action := formalFirstVariationRep32_zero_action_at ε }

/-- Declared formal first-variation operator bundle (fixed-step specialization). -/
def formalFirstVariationRep32 : FormalFirstVariationRep32 :=
  formalFirstVariationRep32At rep32Step rep32Step_ne_zero

/-- Boundary: firstVariationRep32 matches the formal action variation (parameterized by ε). -/
def ActionVariationBridgeRep32At (ε : ℝ) (hε : ε ≠ 0) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    firstVariationRep32 δ ψ =
      (formalFirstVariationRep32At ε hε).op actionRep32.action δ ψ

/-- Boundary: fixed-step specialization of the ε-parameterized bridge. -/
def ActionVariationBridgeRep32 : Prop :=
  ActionVariationBridgeRep32At rep32Step rep32Step_ne_zero

theorem ActionVariationBridgeRep32_of_at
    (h : ActionVariationBridgeRep32At rep32Step rep32Step_ne_zero) :
    ActionVariationBridgeRep32 := by
  simpa [ActionVariationBridgeRep32] using h

/-- Analytic assumption: finite-difference operator matches pairing with EL (Rep32). -/
def ActionRep32FiniteDifferenceRepresentsEL (ε : ℝ) (_hε : ε ≠ 0) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε actionRep32.action δ ψ =
      pairingRep32' (actionRep32.EL ψ) (δ ψ)

/-- Sub-predicate: finite-difference operator matches pairing with `P_rep32`. -/
def ActionRep32FiniteDifferenceRepresentsP (ε : ℝ) (_hε : ε ≠ 0) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε actionRep32.action δ ψ =
      pairingRep32' (P_rep32 ψ) (δ ψ)

/-- Sub-predicate: EL equals the comparison operator on the quotient. -/
def ActionRep32ELMatchesP : Prop :=
  ∀ ψ : FieldRep32, actionRep32.EL ψ = P_rep32 ψ

/-- Sub-predicate: pairing agrees for EL vs `P_rep32` on the quotient. -/
def ActionRep32PairingRespectsELP : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    pairingRep32' (actionRep32.EL ψ) (δ ψ) =
      pairingRep32' (P_rep32 ψ) (δ ψ)

theorem ActionRep32PairingRespectsELP_of_matchesP
    (h : ActionRep32ELMatchesP) : ActionRep32PairingRespectsELP := by
  intro δ ψ
  simp [h ψ]

theorem ActionRep32ELMatchesP_of_rep32 : ActionRep32ELMatchesP := by
  intro ψ
  have h := congrArg (fun f => f ψ) EL_toe_eq_P_rep32
  simpa [EL_toe_rep32] using h

theorem ActionRep32PairingRespectsELP_of_rep32 : ActionRep32PairingRespectsELP :=
  ActionRep32PairingRespectsELP_of_matchesP ActionRep32ELMatchesP_of_rep32

theorem ActionRep32FiniteDifferenceRepresentsEL_of_parts
    (ε : ℝ) (hε : ε ≠ 0)
    (hfd : ActionRep32FiniteDifferenceRepresentsP ε hε)
    (hpair : ActionRep32PairingRespectsELP) :
    ActionRep32FiniteDifferenceRepresentsEL ε hε := by
  intro δ ψ
  have hfd' := hfd δ ψ
  have hpair' := hpair δ ψ
  exact hfd'.trans hpair'.symm

theorem ActionRep32FiniteDifferenceRepresentsEL_of_rep32
    (ε : ℝ) (hε : ε ≠ 0)
    (hfd : ActionRep32FiniteDifferenceRepresentsP ε hε) :
    ActionRep32FiniteDifferenceRepresentsEL ε hε := by
  exact
    ActionRep32FiniteDifferenceRepresentsEL_of_parts ε hε hfd
      ActionRep32PairingRespectsELP_of_rep32

theorem ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL
    (ε : ℝ) (hε : ε ≠ 0)
    (h : ActionRep32FiniteDifferenceRepresentsEL ε hε) :
    ActionVariationBridgeRep32At ε hε := by
  intro δ ψ
  have hrep := actionRep32.represents_EL δ ψ
  exact hrep.trans (h δ ψ).symm

end

end Variational
end ToeFormal
