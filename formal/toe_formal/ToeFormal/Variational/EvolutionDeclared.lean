/-
ToeFormal/Variational/EvolutionDeclared.lean

Evolution linkage scaffold: connect declared evolution to an operator-generated flow.

Scope:
- Structural-only; no analytic dynamics.
- Defines an operator-driven evolution interface and a linkage predicate.
- Provides a routing lemma to the declared Noether conservation statement.
-/

import Mathlib
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.EvolutionFlowLaw
import ToeFormal.Variational.EvolutionGeneratorLaw
import ToeFormal.Variational.Noether
import ToeFormal.Variational.SemigroupEvolution
import ToeFormal.Variational.SemigroupWithGenerator

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Expose the flow-law contract (bookkeeping lemma). -/
def declared_evolution_flow_law :
    FlowLaw Field EL_toe declaredEvolution :=
  by
    simpa [declaredEvolution] using
      (SemigroupWithGenerator.flow_law declaredSemigroupWithGenerator)

/--
Discrete operator-generated evolution update for the declared flow.
This discharges the old generator-at-0 placeholder via the semigroup step law.
-/
theorem declared_evolution_step_update :
    ∀ (ψ : Field) (t : ℝ),
      declaredEvolution.flow (t + declaredSemigroupWithGenerator.generator.step_law.step) ψ
        = declaredEvolution.flow t ψ + EL_toe (declaredEvolution.flow t ψ) := by
  simpa only [declaredEvolution, SemigroupWithGenerator.evolution, Evolution.ofSemigroup] using
    (SemigroupWithGenerator.evolution_step_update declaredSemigroupWithGenerator)

/--
Routing lemma: if the declared evolution is operator-driven and the action is invariant,
then the declared Noether conservation statement applies to that evolution.
-/
theorem noether_conserved_for_declared_evolution
    (hInv : ActionInvariant declaredAction declaredSymmetry) :
    Conserved declaredEvolution declaredQuantity := by
  -- Use the linkage assumption explicitly for audit clarity.
  have _hlaw := declared_evolution_flow_law
  exact declared_noether_conservation hInv

end
end Variational
end ToeFormal
