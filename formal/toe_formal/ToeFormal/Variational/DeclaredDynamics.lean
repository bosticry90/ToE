/-
ToeFormal/Variational/DeclaredDynamics.lean

Phase 1/3 closure shim: canonical declared dynamics object and Noether routing.

Scope:
- Structural-only; does not assert analytic PDE correctness.
- Pins a canonical "declared dynamics" symbol to the declared EL operator.
- Exposes the operator-driven flow law and a routed conserved-quantity lemma.
- Keeps assumptions explicit via the existing declared-action/evolution modules.
-/

import Mathlib
import ToeFormal.Variational.DeclaredAction
import ToeFormal.Variational.EvolutionDeclared
import ToeFormal.Variational.EvolutionFlowLaw

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Canonical declared dynamics operator for the variational lane. -/
def declaredDynamics : Field -> Field :=
  EL_toe

/-- Definitional identity: declared dynamics is the declared EL operator. -/
@[simp] theorem declaredDynamics_eq :
    declaredDynamics = EL_toe :=
  rfl

/-- Declared evolution satisfies the operator-driven flow law for declared dynamics. -/
theorem declared_dynamics_flow_law :
    FlowLaw Field declaredDynamics declaredEvolution := by
  simpa [declaredDynamics] using declared_evolution_flow_law

/-- Canonical invariant candidate routed along declared evolution. -/
def declaredInvariant : Field -> ℝ :=
  declaredQuantity

/--
If the declared action is invariant under the declared symmetry,
the declared invariant is conserved along the declared evolution.
-/
theorem declared_invariant_conserved
    (hInv : ActionInvariant declaredAction declaredSymmetry) :
    Conserved declaredEvolution declaredInvariant := by
  simpa [declaredInvariant] using noether_conserved_for_declared_evolution hInv

end Variational
end ToeFormal
