/-
ToeFormal/Variational/EvolutionFlowLaw.lean

Structural flow-law interface tying an evolution flow to an operator.

Scope:
- Structural-only; no analytic dynamics.
- Introduces an abstract time-derivative operator and a compatibility law.
-/

import Mathlib
import ToeFormal.Variational.Noether

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/--
Flow-law contract: an abstract time-derivative operator that makes the flow
an integral-curve-style evolution for the operator `Op`.
-/
structure FlowLaw (F : Type) (Op : F -> F) (E : Evolution F) : Type where
  timeDerivative : (ℝ -> F) -> ℝ -> F
  dynamics : ∀ (ψ : F) (t : ℝ),
    timeDerivative (fun τ => E.flow τ ψ) t = Op (E.flow t ψ)

/-- Strong operator-driven evolution: generator equality + explicit flow law. -/
structure EvolutionFromOperatorStrong (F : Type) (Op : F -> F) (E : Evolution F) : Type where
  generator : F -> F
  generator_eq : generator = Op
  flow_law : FlowLaw F Op E

end
end Variational
end ToeFormal
