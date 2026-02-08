/-
ToeFormal/Variational/EvolutionGeneratorLaw.lean

Discrete generator-law contract for semigroup evolutions (structural-only).

Scope:
- Replaces derivative-at-0 assumptions with a fixed-step finite-difference generator.
- Derives a non-tautological one-step evolution update from semigroup + generator law.
- Bundles discrete generator law with the existing flow-law contract.
- No analytic content; all assumptions are structural.
-/

import Mathlib
import ToeFormal.Variational.SemigroupEvolution

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Fixed-step finite-difference generator induced by a semigroup flow. -/
def StepGenerator (F : Type) [Sub F] (S : FlowSemigroup F) (step : ℝ) : F -> F :=
  fun ψ => S.flow step ψ - ψ

/--
Discrete generator law: the operator is defined by a fixed nonzero flow step
(`Op ψ = flow(step, ψ) - ψ`).
-/
structure GeneratorStepLaw (F : Type) [Sub F] (Op : F -> F) (S : FlowSemigroup F) : Prop where
  step : ℝ
  step_ne_zero : step ≠ 0
  law : ∀ ψ : F, Op ψ = StepGenerator F S step ψ

/-- One-step update form induced by `GeneratorStepLaw`. -/
theorem GeneratorStepLaw.flow_step_eq_add
    {F : Type} [AddGroup F] {Op : F -> F} {S : FlowSemigroup F}
    (h : GeneratorStepLaw F Op S) :
    ∀ ψ : F, S.flow h.step ψ = ψ + Op ψ := by
  intro ψ
  have hs : S.flow h.step ψ - ψ = Op ψ := by
    simpa [StepGenerator] using (h.law ψ).symm
  exact (sub_eq_iff_eq_add').mp hs

/--
Discrete evolution update along the semigroup:
`flow(t + step, ψ) = flow(t, ψ) + Op(flow(t, ψ))`.
-/
theorem GeneratorStepLaw.evolution_step_update
    {F : Type} [AddCommGroup F] {Op : F -> F} {S : FlowSemigroup F}
    (h : GeneratorStepLaw F Op S) :
    ∀ (ψ : F) (t : ℝ),
      S.flow (t + h.step) ψ = S.flow t ψ + Op (S.flow t ψ) := by
  intro ψ t
  calc
    S.flow (t + h.step) ψ = S.flow (h.step + t) ψ := by simpa [add_comm]
    _ = S.flow h.step (S.flow t ψ) := by simpa using S.flow_add h.step t ψ
    _ = S.flow t ψ + Op (S.flow t ψ) := by
      simpa using (h.flow_step_eq_add (S.flow t ψ))

/--
Strong generator law: combines the discrete generator contract with the existing flow-law
contract for the semigroup evolution.
-/
structure GeneratorLawStrong (F : Type) [Sub F] (Op : F -> F) (S : FlowSemigroup F) : Prop where
  step_law : GeneratorStepLaw F Op S
  flow_law : GeneratorLaw Op S

end Variational
end ToeFormal
