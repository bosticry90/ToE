import ToeFormal.Constraints.AD01_Instances

namespace ToeFormal
namespace Constraints

open ToeFormal.OperatorCore
open ToeFormal.Constraints
open ToeFormal.Constraints.CAUS01
open ToeFormal.CPNLSE2D
open ToeFormal.Constraints.AD01

/--
Consequence test:
If operator metadata declares `secondOrderTime` while the canonical AD01 suite fixes
`G0.form = firstOrderTime`, then the AD01 CAUS gate rejects it (via `TimeOrderSaneOp`).

This is purely a metadata consistency check (non-analytic).
-/
theorem ad01_caus_rejects_second_order_time
  (O : Op2D) :
  ¬ @TimeOrderSaneOp G0.form Field2D
      { timeOrder := fun _ => EvolForm.secondOrderTime } O := by
  intro hTo
  simp [TimeOrderSaneOp, G0] at hTo

end Constraints
end ToeFormal
