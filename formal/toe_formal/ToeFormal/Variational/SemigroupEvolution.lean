/-
ToeFormal/Variational/SemigroupEvolution.lean

Semigroup-based evolution wrapper (structural-only).

Scope:
- Defines a flow semigroup on F.
- Provides Evolution.ofSemigroup.
- Defines GeneratorLaw tying an operator to the semigroup flow via FlowLaw.
-/

import Mathlib
import ToeFormal.Variational.EvolutionFlowLaw

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Flow semigroup on F: time-parameterized maps with identity and additivity. -/
structure FlowSemigroup (F : Type) where
  flow : ℝ -> F -> F
  flow_zero : ∀ ψ : F, flow 0 ψ = ψ
  flow_add : ∀ (t1 t2 : ℝ) (ψ : F), flow (t1 + t2) ψ = flow t1 (flow t2 ψ)

/-- Build an Evolution from a flow semigroup. -/
def Evolution.ofSemigroup {F : Type} (S : FlowSemigroup F) : Evolution F :=
  { flow := S.flow
    flow_zero := S.flow_zero
    flow_add := S.flow_add }

/-- Generator law: the operator governs the semigroup flow (abstract). -/
def GeneratorLaw {F : Type} (Op : F -> F) (S : FlowSemigroup F) : Type :=
  FlowLaw F Op (Evolution.ofSemigroup S)

end
end Variational
end ToeFormal
