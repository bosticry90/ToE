import Mathlib
import ToeFormal.OperatorCore.OperatorSignature
import ToeFormal.Constraints.CAUS01_CausalityGate

namespace ToeFormal
namespace OperatorCore

open ToeFormal.Constraints.CAUS01

/--
Minimal non-analytic metadata tag:
declares which evolution form an operator is intended to belong to.
This is a semantic label, not inferred from the function body.
-/
class OpTimeOrder (F : Type) where
  timeOrder : Op2D → EvolForm

/-- Structural sanity: operator’s declared time-order matches the gate’s declared form. -/
def TimeOrderSaneOp (form : EvolForm) {F : Type} [OpTimeOrder F] (O : Op2D) : Prop :=
  OpTimeOrder.timeOrder (F := F) O = form

end OperatorCore
end ToeFormal
