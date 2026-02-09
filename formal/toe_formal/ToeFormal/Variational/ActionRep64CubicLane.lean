/-
ToeFormal/Variational/ActionRep64CubicLane.lean

Rep64 cubic action lane wiring (structural-only, assumption-scoped).

Scope:
- Reuses the proven Rep32 cubic lane bridge shape on an additional Rep64 lane.
- Keeps assumptions explicit and RAC-scoped.
- No analytic claims; no physics truth-claim upgrade.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.ActionRep32CubicLane
import ToeFormal.Variational.DischargeELMatchesFN01Rep64Pcubic

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-- Rep64 RAC package reuses the Rep32 cubic remainder policy surface. -/
def RAC_Rep64_Cubic (g : ℂ) : Prop :=
  RAC_Rep32_Cubic g

structure Rep64CubicLaneAssumptions (ε : ℝ) : Prop where
  hε : ε ≠ 0
  hAction : actionRep32.action = actionRep32Cubic declared_g_rep64
  hP : P_rep32 = P_cubic_rep32_def declared_g_rep64
  hRAC : RAC_Rep64_Cubic declared_g_rep64

theorem Rep64_cubic_lane_declared
    (ε : ℝ)
    (h : Rep64CubicLaneAssumptions ε) :
    ActionVariationBridgeRep32At ε h.hε ∧
      EL_toe_rep64 = P_cubic_rep64 declared_g_rep64 := by
  have hBridge : ActionVariationBridgeRep32At ε h.hε :=
    (Rep32_cubic_lane_declared_g ε h.hε h.hAction h.hP h.hRAC).1
  have hEL : EL_toe_rep64 = P_cubic_rep64 declared_g_rep64 :=
    EL_toe_eq_Pcubic_rep64
  exact ⟨hBridge, hEL⟩

end

end Variational
end ToeFormal
