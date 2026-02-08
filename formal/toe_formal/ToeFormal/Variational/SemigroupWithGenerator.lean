/-
ToeFormal/Variational/SemigroupWithGenerator.lean

Unified semigroup + generator contract (structural-only).

Scope:
- Packages a flow semigroup together with a strengthened generator law.
- Exposes a definitional Evolution built from the semigroup.
- Provides a flow-law projection for downstream routing.
-/

import Mathlib
import ToeFormal.Variational.EvolutionGeneratorLaw
import ToeFormal.Variational.SemigroupEvolution

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Semigroup packaged with a strengthened generator law (structural-only). -/
structure SemigroupWithGenerator (F : Type) [Sub F] (Op : F -> F) where
  semigroup : FlowSemigroup F
  generator : GeneratorLawStrong F Op semigroup

/-- Definitional evolution from the packaged semigroup. -/
def SemigroupWithGenerator.evolution {F : Type} [Sub F] {Op : F -> F}
    (G : SemigroupWithGenerator F Op) : Evolution F :=
  Evolution.ofSemigroup G.semigroup

/-- Flow-law projection from the strengthened generator law. -/
def SemigroupWithGenerator.flow_law {F : Type} [Sub F] {Op : F -> F}
    (G : SemigroupWithGenerator F Op) :
    FlowLaw F Op (SemigroupWithGenerator.evolution G) := by
  simpa [SemigroupWithGenerator.evolution] using G.generator.flow_law

/--
Discrete one-step evolution update projection:
`flow(t + step, ψ) = flow(t, ψ) + Op(flow(t, ψ))`.
-/
theorem SemigroupWithGenerator.evolution_step_update
    {F : Type} [AddCommGroup F] {Op : F -> F}
    (G : SemigroupWithGenerator F Op) :
    ∀ (ψ : F) (t : ℝ),
      G.semigroup.flow (t + G.generator.step_law.step) ψ
        = G.semigroup.flow t ψ + Op (G.semigroup.flow t ψ) := by
  simpa using (GeneratorStepLaw.evolution_step_update G.generator.step_law)

end
end Variational
end ToeFormal
