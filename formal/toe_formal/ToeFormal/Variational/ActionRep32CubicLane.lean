/-
ToeFormal/Variational/ActionRep32CubicLane.lean

Rep32 cubic action lane wiring (structural-only, assumption-scoped).

Scope:
- Pins the Rep32 action to the cubic action class (assumption).
- Pins `P_rep32` to the cubic representer (via the existing Rep32 stub).
- Packages cubic remainder predicates into a single RAC-style assumption.
- Discharges the finite-difference bridge under those explicit predicates.
- Provides an end-to-end theorem: ε-bridge + EL-to-P_cubic identification.
- No analytic claims; all assumptions are explicit.
-/

import Mathlib
import ToeFormal.Constraints.FN01_CandidateAPI
import ToeFormal.Variational.ActionToFirstVariationBridgeRep32
import ToeFormal.Variational.ActionRep32QuadraticCubic
import ToeFormal.Variational.DischargeELMatchesFN01Rep32Pcubic

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-! ### RAC-style cubic remainder package -/

def RAC_Rep32_Cubic (g : ℂ) : Prop :=
  ActionRep32CubicLinearMatchesP g ∧
  ActionRep32CubicNoSecondOrder g ∧
  ActionRep32CubicNoThirdOrder g ∧
  ActionRep32CubicNoFourthOrder g

/-! ### Assumption package for the cubic lane -/

structure Rep32CubicLaneAssumptions (g : ℂ) (ε : ℝ) : Prop where
  hε : ε ≠ 0
  hAction : actionRep32.action = actionRep32Cubic g
  hP : P_rep32 = P_cubic_rep32_def g
  hRAC : RAC_Rep32_Cubic g

/-! ### Bridge discharge under RAC -/

theorem ActionRep32FiniteDifferenceRepresentsP_cubic_of_RAC
    (g : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hRAC : RAC_Rep32_Cubic g) :
    ActionRep32FiniteDifferenceRepresentsP ε hε := by
  rcases hRAC with ⟨h1, h2, h3, h4⟩
  exact
    ActionRep32FiniteDifferenceRepresentsP_of_cubic g
      hAction hP h1 h2 h3 h4 ε hε

theorem ActionVariationBridgeRep32At_cubic_of_RAC
    (g : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hRAC : RAC_Rep32_Cubic g) :
    ActionVariationBridgeRep32At ε hε := by
  have hfd :=
    ActionRep32FiniteDifferenceRepresentsP_cubic_of_RAC g ε hε hAction hP hRAC
  have hEL := ActionRep32FiniteDifferenceRepresentsEL_of_rep32 ε hε hfd
  exact ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL ε hε hEL

/-! ### End-to-end Rep32 cubic lane result -/

theorem Rep32_cubic_lane'
    (g : ℂ) (ε : ℝ)
    (h : Rep32CubicLaneAssumptions g ε) :
    ActionVariationBridgeRep32At ε h.hε ∧
      EL_toe_rep32 = P_cubic_rep32_def g := by
  have hBridge :=
    ActionVariationBridgeRep32At_cubic_of_RAC g ε h.hε h.hAction h.hP h.hRAC
  have hEL : EL_toe_rep32 = P_cubic_rep32_def g := by
    simpa [h.hP] using EL_toe_eq_P_rep32
  exact ⟨hBridge, hEL⟩

theorem Rep32_cubic_lane_declared
    (g : ℂ) (ε : ℝ)
    (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hRAC : RAC_Rep32_Cubic g) :
    ActionVariationBridgeRep32At ε hε ∧
      EL_toe_rep32 = P_cubic_rep32_def g := by
  exact
    Rep32_cubic_lane' g ε
      { hε := hε, hAction := hAction, hP := hP, hRAC := hRAC }

theorem Rep32_cubic_lane_declared_g
    (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32) :
    ActionVariationBridgeRep32At ε hε ∧
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  simpa using
    (Rep32_cubic_lane_declared (g := declared_g_rep32)
      (ε := ε) (hε := hε) (hAction := hAction) (hP := hP) (hRAC := hRAC))

end

end Variational
end ToeFormal
