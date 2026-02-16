/-
ToeFormal/QM/MeasurementSemantics.lean

Planning-surface theorem contract for QM measurement semantics.

Scope:
- Contract-only theorem surface.
- Typed measurement/probability objects only.
- Structural normalization contract under explicit assumptions.
- No Born-rule claim and no external truth claim.
-/

import Mathlib

namespace ToeFormal
namespace QM

noncomputable section
set_option autoImplicit false
open scoped BigOperators

structure OutcomeSpace (Outcome : Type) [DecidableEq Outcome] where
  support : Finset Outcome
  support_nonempty : support.Nonempty

structure MeasurementContext (State Outcome : Type) [DecidableEq Outcome] where
  outcomeSpace : OutcomeSpace Outcome
  observable : State → Outcome → Real

structure ProbabilityMap (State Outcome : Type) [DecidableEq Outcome]
    (ctx : MeasurementContext State Outcome) where
  weights : State → Outcome → Real
  nonneg_support : ∀ s : State, ∀ o : Outcome, o ∈ ctx.outcomeSpace.support → 0 ≤ weights s o

def NormalizedWeights
    {Outcome : Type} [DecidableEq Outcome]
    (outcomeSpace : OutcomeSpace Outcome)
    (w : Outcome → Real) : Prop :=
  (∀ o : Outcome, o ∈ outcomeSpace.support → 0 ≤ w o)
    ∧ (Finset.sum outcomeSpace.support (fun o => w o) = 1)

def Expectation
    {Outcome : Type} [DecidableEq Outcome]
    (outcomeSpace : OutcomeSpace Outcome)
    (w : Outcome → Real)
    (f : Outcome → Real) : Real :=
  Finset.sum outcomeSpace.support (fun o => w o * f o)

def ExpectedObservable
    {State Outcome : Type} [DecidableEq Outcome]
    (ctx : MeasurementContext State Outcome)
    (probabilityMap : ProbabilityMap State Outcome ctx)
    (s : State) : Real :=
  Expectation ctx.outcomeSpace (probabilityMap.weights s) (ctx.observable s)

theorem expectation_add
    {Outcome : Type} [DecidableEq Outcome]
    (outcomeSpace : OutcomeSpace Outcome)
    (w f g : Outcome → Real) :
    Expectation outcomeSpace w (fun o => f o + g o)
      = Expectation outcomeSpace w f + Expectation outcomeSpace w g := by
  unfold Expectation
  simp [mul_add, Finset.sum_add_distrib]

theorem expectation_smul
    {Outcome : Type} [DecidableEq Outcome]
    (outcomeSpace : OutcomeSpace Outcome)
    (w f : Outcome → Real)
    (a : Real) :
    Expectation outcomeSpace w (fun o => a * f o)
      = a * Expectation outcomeSpace w f := by
  unfold Expectation
  simp [mul_left_comm, Finset.mul_sum]

theorem expectation_nonneg_of_nonneg_weights_and_observable
    {Outcome : Type} [DecidableEq Outcome]
    (outcomeSpace : OutcomeSpace Outcome)
    (w f : Outcome → Real)
    (h_w_nonneg : ∀ o : Outcome, o ∈ outcomeSpace.support → 0 ≤ w o)
    (h_f_nonneg : ∀ o : Outcome, o ∈ outcomeSpace.support → 0 ≤ f o) :
    0 ≤ Expectation outcomeSpace w f := by
  unfold Expectation
  exact Finset.sum_nonneg (fun o ho => mul_nonneg (h_w_nonneg o ho) (h_f_nonneg o ho))

theorem weights_eq_zero_extension_of_context_consistency
    (State Outcome : Type)
    [DecidableEq Outcome]
    (ctx : MeasurementContext State Outcome)
    (probabilityMap : ProbabilityMap State Outcome ctx)
    (s : State)
    (h_context_consistency :
      ∀ o : Outcome, o ∉ ctx.outcomeSpace.support → probabilityMap.weights s o = 0) :
    (fun o : Outcome =>
      if o ∈ ctx.outcomeSpace.support then probabilityMap.weights s o else 0)
      = probabilityMap.weights s := by
  funext o
  by_cases ho : o ∈ ctx.outcomeSpace.support
  · simp [ho]
  · simp [ho, h_context_consistency o ho]

theorem expectation_eq_of_context_consistency_with_zero_extension
    (State Outcome : Type)
    [DecidableEq Outcome]
    (ctx : MeasurementContext State Outcome)
    (probabilityMap : ProbabilityMap State Outcome ctx)
    (s : State)
    (h_context_consistency :
      ∀ o : Outcome, o ∉ ctx.outcomeSpace.support → probabilityMap.weights s o = 0)
    (f : Outcome → Real) :
    Expectation ctx.outcomeSpace (probabilityMap.weights s) f
      = Expectation
          ctx.outcomeSpace
          (fun o =>
            if o ∈ ctx.outcomeSpace.support then probabilityMap.weights s o else 0)
          f := by
  have hWeightsEq :
      (fun o : Outcome =>
        if o ∈ ctx.outcomeSpace.support then probabilityMap.weights s o else 0)
        = probabilityMap.weights s :=
    weights_eq_zero_extension_of_context_consistency
      State Outcome ctx probabilityMap s h_context_consistency
  simp [hWeightsEq]

theorem expected_observable_nonneg_of_support_nonneg
    (State Outcome : Type)
    [DecidableEq Outcome]
    (ctx : MeasurementContext State Outcome)
    (probabilityMap : ProbabilityMap State Outcome ctx)
    (s : State)
    (h_observable_nonneg :
      ∀ o : Outcome, o ∈ ctx.outcomeSpace.support → 0 ≤ ctx.observable s o) :
    0 ≤ ExpectedObservable ctx probabilityMap s := by
  unfold ExpectedObservable
  exact
    expectation_nonneg_of_nonneg_weights_and_observable
      ctx.outcomeSpace
      (probabilityMap.weights s)
      (ctx.observable s)
      (fun o ho => probabilityMap.nonneg_support s o ho)
      h_observable_nonneg

theorem qm_measurement_weights_normalized_under_assumptions
    (State Outcome : Type)
    [DecidableEq Outcome]
    (s : State)
    (ctx : MeasurementContext State Outcome)
    (probabilityMap : ProbabilityMap State Outcome ctx)
    (h_context_consistency :
      ∀ o : Outcome, o ∉ ctx.outcomeSpace.support → probabilityMap.weights s o = 0)
    (h_normalization :
      Finset.sum ctx.outcomeSpace.support (fun o => probabilityMap.weights s o) = 1) :
    NormalizedWeights ctx.outcomeSpace (probabilityMap.weights s) := by
  have hBoundary :
      Expectation ctx.outcomeSpace (probabilityMap.weights s) (fun _ : Outcome => (1 : Real))
        = Expectation
            ctx.outcomeSpace
            (fun o =>
              if o ∈ ctx.outcomeSpace.support then probabilityMap.weights s o else 0)
            (fun _ : Outcome => (1 : Real)) :=
    expectation_eq_of_context_consistency_with_zero_extension
      State Outcome ctx probabilityMap s h_context_consistency (fun _ : Outcome => (1 : Real))
  let _ := hBoundary
  exact ⟨fun o ho => probabilityMap.nonneg_support s o ho, h_normalization⟩

end
end QM
end ToeFormal
