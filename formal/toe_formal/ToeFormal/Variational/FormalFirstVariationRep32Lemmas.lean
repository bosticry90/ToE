/-
ToeFormal/Variational/FormalFirstVariationRep32Lemmas.lean

Lemmas for the formal Rep32 first-variation operator.

Scope:
- Restates bundled laws as simp-lemmas.
- Provides finite-sum linearity using the declared variation operations.
- Does not assume additive/scalar structure on FieldRep32.
-/

import Mathlib
import ToeFormal.Variational.ActionToFirstVariationBridgeRep32

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

@[simp] theorem op_zeroVar
    (A : FieldRep32 -> ℝ) (ψ : FieldRep32) :
    (formalFirstVariationRep32.op) A formalFirstVariationRep32.zeroVar ψ = 0 :=
  formalFirstVariationRep32.zero_variation A ψ

@[simp] theorem op_addVar
    (A : FieldRep32 -> ℝ) (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    (formalFirstVariationRep32.op) A
        (formalFirstVariationRep32.addVar δ₁ δ₂) ψ =
      (formalFirstVariationRep32.op) A δ₁ ψ +
      (formalFirstVariationRep32.op) A δ₂ ψ :=
  formalFirstVariationRep32.add_variation A δ₁ δ₂ ψ

@[simp] theorem op_smulVar
    (A : FieldRep32 -> ℝ) (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    (formalFirstVariationRep32.op) A
        (formalFirstVariationRep32.smulVar c δ) ψ =
      c * (formalFirstVariationRep32.op) A δ ψ :=
  formalFirstVariationRep32.smul_variation A c δ ψ

@[simp] theorem op_zero_action
    (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    (formalFirstVariationRep32.op) (fun _ => (0 : ℝ)) δ ψ = 0 :=
  formalFirstVariationRep32.zero_action δ ψ

theorem firstVariationRep32_addVar
    (h : ActionVariationBridgeRep32)
    (δ₁ δ₂ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    firstVariationRep32 (formalFirstVariationRep32.addVar δ₁ δ₂) ψ =
      firstVariationRep32 δ₁ ψ + firstVariationRep32 δ₂ ψ := by
  have h' :
      ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
        firstVariationRep32 δ ψ =
          (formalFirstVariationRep32.op) actionRep32.action δ ψ := by
    simpa [ActionVariationBridgeRep32] using h
  simp [h']

theorem firstVariationRep32_smulVar
    (h : ActionVariationBridgeRep32)
    (c : ℝ) (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32) :
    firstVariationRep32 (formalFirstVariationRep32.smulVar c δ) ψ =
      c * firstVariationRep32 δ ψ := by
  have h' :
      ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
        firstVariationRep32 δ ψ =
          (formalFirstVariationRep32.op) actionRep32.action δ ψ := by
    simpa [ActionVariationBridgeRep32] using h
  simp [h']

theorem firstVariationRep32_zeroVar
    (h : ActionVariationBridgeRep32) (ψ : FieldRep32) :
    firstVariationRep32 formalFirstVariationRep32.zeroVar ψ = 0 := by
  have h' :
      ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
        firstVariationRep32 δ ψ =
          (formalFirstVariationRep32.op) actionRep32.action δ ψ := by
    simpa [ActionVariationBridgeRep32] using h
  simp [h']

/-- Fold a list of variations using the declared operations. -/
def foldVarList {α : Type} (l : List α) (f : α -> FieldRep32 -> FieldRep32) :
    FieldRep32 -> FieldRep32 :=
  l.foldr (fun a acc => formalFirstVariationRep32.addVar (f a) acc)
    formalFirstVariationRep32.zeroVar

/-- Linearity over a folded list of variations (with declared operations). -/
theorem op_foldVarList {α : Type}
    (A : FieldRep32 -> ℝ) (ψ : FieldRep32) (l : List α)
    (f : α -> FieldRep32 -> FieldRep32) :
    (formalFirstVariationRep32.op) A (foldVarList l f) ψ =
      l.foldr (fun a acc => (formalFirstVariationRep32.op) A (f a) ψ + acc) 0 := by
  induction l with
  | nil =>
      simp [foldVarList, op_zeroVar]
  | cons a l ih =>
      simpa [foldVarList, op_addVar] using ih

/-- If a representation holds, it respects the declared variation operations. -/
theorem represents_respects_variations
    (A : FieldRep32 -> ℝ) (ψ : FieldRep32)
    (δ₁ δ₂ : FieldRep32 -> FieldRep32) (c : ℝ) :
    (formalFirstVariationRep32.op) A
        (formalFirstVariationRep32.addVar δ₁ δ₂) ψ =
      (formalFirstVariationRep32.op) A δ₁ ψ +
      (formalFirstVariationRep32.op) A δ₂ ψ ∧
    (formalFirstVariationRep32.op) A
        (formalFirstVariationRep32.smulVar c δ₁) ψ =
      c * (formalFirstVariationRep32.op) A δ₁ ψ := by
  constructor
  · exact op_addVar A δ₁ δ₂ ψ
  · exact op_smulVar A c δ₁ ψ

end

end Variational
end ToeFormal
