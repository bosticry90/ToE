/-
ToeFormal/Variational/ActionInvariance.lean

Structural lemma: termwise invariance under SYM-01 phase action
implies action invariance (weighted sum).

Scope:
- Structural-only; no analytic content.
- Provides a discharge path for ActionInvariant assumptions.
-/

import Mathlib
import ToeFormal.Variational.ActionScaffold
import ToeFormal.Variational.Noether
import ToeFormal.Constraints.SYM01_PhaseInvariant

namespace ToeFormal
namespace Variational

universe u

noncomputable section
set_option autoImplicit false

/-- One-parameter action induced by a SYM-01 phase action. -/
def oneParamAction_of_SYM01 {F : Type u} (A : Constraints.SYM01.PhaseAction F) :
    OneParameterAction F :=
  { act := A.act
    act_zero := A.act_zero
    act_add := A.act_add }

/-- Termwise invariance for scalar-valued functionals under a phase action. -/
def TermInvariant {F : Type u} (A : Constraints.SYM01.PhaseAction F) (f : F → ℝ) : Prop :=
  ∀ (θ : ℝ) (ψ : F), f (A.act θ ψ) = f ψ

/--
If each action ingredient is invariant under the phase action, then the
weighted action is invariant.
-/
theorem action_invariant_of_terms
    {F : Type u}
    (A : Constraints.SYM01.PhaseAction F)
    (S : ActionScaffold F)
    (hK : TermInvariant A S.kinetic)
    (hD : TermInvariant A S.dispersion)
    (hC : TermInvariant A S.coherence) :
    ActionInvariant S (oneParamAction_of_SYM01 A) := by
  intro θ ψ
  have hK' : S.kinetic (A.act θ ψ) = S.kinetic ψ := hK θ ψ
  have hD' : S.dispersion (A.act θ ψ) = S.dispersion ψ := hD θ ψ
  have hC' : S.coherence (A.act θ ψ) = S.coherence ψ := hC θ ψ
  -- Expand the action and rewrite by termwise invariance.
  simp [action, oneParamAction_of_SYM01, hK', hD', hC']

end
end Variational
end ToeFormal
