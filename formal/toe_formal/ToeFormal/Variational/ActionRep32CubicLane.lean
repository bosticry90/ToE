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

theorem actionRep32_action_default_binding :
    actionRep32.action = actionRep32Cubic declared_g_rep32 := by
  funext ψ
  change pairingRep32' (P_rep32 ψ) ψ =
    pairingRep32' (P_cubic_rep32_def declared_g_rep32 ψ) ψ
  simpa using congrArg (fun f => pairingRep32' (f ψ) ψ) P_rep32_def

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

abbrev ActionRep32CubicDeviationZeroAtStep (g : ℂ) (ε : ℝ) : Prop :=
  ActionRep32CubicTotalDeviationZeroAtStep g ε

theorem ActionRep32CubicDeviationZeroAtStep_of_RAC
    (g : ℂ) (ε : ℝ)
    (hRAC : RAC_Rep32_Cubic g) :
    ActionRep32CubicDeviationZeroAtStep g ε := by
  rcases hRAC with ⟨h1, h2, h3, h4⟩
  exact
    ActionRep32CubicTotalDeviationZeroAtStep_of_components
      g
      ε
      h1
      h2
      h3
      h4

theorem ActionRep32FiniteDifferenceRepresentsP_cubic_of_deviationZeroAtStep
    (g : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep g ε) :
    ActionRep32FiniteDifferenceRepresentsP ε hε := by
  exact
    ActionRep32FiniteDifferenceRepresentsP_of_cubic_totalDeviationZeroAtStep
      g
      hAction
      hP
      ε
      hε
      hDevZero

theorem ActionVariationBridgeRep32At_cubic_of_RAC
    (g : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hRAC : RAC_Rep32_Cubic g) :
    ActionVariationBridgeRep32At ε hε := by
  have hDevZero : ActionRep32CubicDeviationZeroAtStep g ε :=
    ActionRep32CubicDeviationZeroAtStep_of_RAC g ε hRAC
  have hfd :
      ActionRep32FiniteDifferenceRepresentsP ε hε :=
    ActionRep32FiniteDifferenceRepresentsP_cubic_of_deviationZeroAtStep
      g
      ε
      hε
      hAction
      hP
      hDevZero
  have hEL : ActionRep32FiniteDifferenceRepresentsEL ε hε :=
    ActionRep32FiniteDifferenceRepresentsEL_of_rep32 ε hε hfd
  exact ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL ε hε hEL

theorem ActionVariationBridgeRep32At_cubic_of_deviationZeroAtStep
    (g : ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep g ε) :
    ActionVariationBridgeRep32At ε hε := by
  have hfd :
      ActionRep32FiniteDifferenceRepresentsP ε hε :=
    ActionRep32FiniteDifferenceRepresentsP_cubic_of_deviationZeroAtStep
      g
      ε
      hε
      hAction
      hP
      hDevZero
  have hEL : ActionRep32FiniteDifferenceRepresentsEL ε hε :=
    ActionRep32FiniteDifferenceRepresentsEL_of_rep32 ε hε hfd
  exact ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL ε hε hEL

theorem ActionRep32FiniteDifferenceDeviationFromP_default_binding
    (ε : ℝ) (hε : ε ≠ 0) :
    ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      formalFirstVariationRep32OpAt ε actionRep32.action δ ψ -
        pairingRep32' (P_rep32 ψ) (δ ψ) =
          cubicLinearDeviation declared_g_rep32 δ ψ +
            ε * cubicRemainder₂ declared_g_rep32 δ ψ +
            ε^2 * cubicRemainder₃ declared_g_rep32 δ ψ +
            ε^3 * cubicRemainder₄ declared_g_rep32 δ ψ := by
  exact
    ActionRep32FiniteDifferenceDeviationFromP_of_cubic
      declared_g_rep32
      actionRep32_action_default_binding
      P_rep32_def
      ε
      hε

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

theorem Rep32_cubic_lane_default_binding
    (ε : ℝ) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32) :
    ActionVariationBridgeRep32At ε hε ∧
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  exact
    Rep32_cubic_lane_declared_g
      ε
      hε
      actionRep32_action_default_binding
      P_rep32_def
      hRAC

/-!
Compatibility aliases/tokens used by downstream GR01 theorem-surface modules.
-/

abbrev RACRep32CubicObligationSet (g : ℂ) : Prop := RAC_Rep32_Cubic g

theorem EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions
    (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  let _ := ε
  let _ := hε
  let _ := hAction
  let _ := hRAC
  simpa [P_rep32_def] using EL_toe_eq_P_rep32

theorem EL_toe_rep32_equals_Pcubic_under_default_binding_assumptions
    (ε : ℝ) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  let _ := ε
  let _ := hε
  let _ := hRAC
  simpa [P_rep32_def] using EL_toe_eq_P_rep32

theorem EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_of_hP
    (ε : ℝ) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  let _ := ε
  let _ := hε
  let _ := hAction
  let _ := hRAC
  simpa [hP] using EL_toe_eq_P_rep32

theorem EL_toe_rep32_equals_Pcubic_under_default_binding_assumptions_of_hP
    (ε : ℝ) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  let _ := ε
  let _ := hε
  let _ := hRAC
  simpa [hP] using EL_toe_eq_P_rep32

end

end Variational
end ToeFormal
