/-
ToeFormal/Bridges/QM_STAT_Transport.lean

Strict physics theorem-body components for the QM-STAT seam.

Scope:
- finite-state transport lemmas for entropy-like sums and moments
- no DER01/DER02 replay
- no seam-closure, entropy-law, Born-rule, or empirical claim
- no governance/status promotion

These lemmas isolate one hard requirement for the QM-STAT seam: a transport map
must preserve the statistical quantities it is later asked to compare.
-/

import Mathlib

namespace ToeFormal
namespace Bridges
namespace QMSTATTransport

noncomputable section
open scoped BigOperators
set_option autoImplicit false

/-- Entropy-like finite sum for any pointwise weight, including Shannon-style weights. -/
def EntropyLike {State : Type} [Fintype State]
    (weight : Real → Real) (probability : State → Real) : Real :=
  ∑ state, weight (probability state)

/-- Finite expectation moment for an observable against a probability weight. -/
def Moment {State : Type} [Fintype State]
    (observable probability : State → Real) : Real :=
  ∑ state, observable state * probability state

/-- Variance from mean and second moment. -/
def Variance (mean secondMoment : Real) : Real :=
  secondMoment - mean ^ 2

/--
An invertible finite-state transport preserves any entropy-like sum whose
target probability is the transported source probability.
-/
theorem entropyLike_preserved_under_equiv
    {State : Type} [Fintype State]
    (weight : Real → Real)
    (transport : State ≃ State)
    (source target : State → Real)
    (hTransport : ∀ state : State, target state = source (transport state)) :
    EntropyLike weight target = EntropyLike weight source := by
  unfold EntropyLike
  calc
    (∑ state, weight (target state)) =
        ∑ state, weight (source (transport state)) := by
      simp [hTransport]
    _ = ∑ state, weight (source state) := by
      exact Fintype.sum_equiv transport
        (fun state => weight (source (transport state)))
        (fun state => weight (source state))
        (by intro state; rfl)

/--
Moments are preserved when both the probability and observable are transported
through the same invertible state map.
-/
theorem moment_preserved_under_equiv
    {State : Type} [Fintype State]
    (transport : State ≃ State)
    (sourceProbability targetProbability sourceObservable targetObservable : State → Real)
    (hProbability :
      ∀ state : State, targetProbability state = sourceProbability (transport state))
    (hObservable :
      ∀ state : State, targetObservable state = sourceObservable (transport state)) :
    Moment targetObservable targetProbability =
      Moment sourceObservable sourceProbability := by
  unfold Moment
  calc
    (∑ state, targetObservable state * targetProbability state) =
        ∑ state, sourceObservable (transport state) * sourceProbability (transport state) := by
      simp [hProbability, hObservable]
    _ = ∑ state, sourceObservable state * sourceProbability state := by
      exact Fintype.sum_equiv transport
        (fun state => sourceObservable (transport state) * sourceProbability (transport state))
        (fun state => sourceObservable state * sourceProbability state)
        (by intro state; rfl)

/-- Preserved first and second moments preserve variance. -/
theorem variance_preserved_from_moment_transport
    (sourceMean targetMean sourceSecondMoment targetSecondMoment : Real)
    (hMean : targetMean = sourceMean)
    (hSecond : targetSecondMoment = sourceSecondMoment) :
    Variance targetMean targetSecondMoment =
      Variance sourceMean sourceSecondMoment := by
  unfold Variance
  rw [hMean, hSecond]

end
end QMSTATTransport
end Bridges
end ToeFormal
