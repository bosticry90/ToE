/-
ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean

Action-to-operator discrete derivation pressure sequence for GR01.

Scope:
- Bounded/discrete only.
- No continuum-limit claim.
- No uniqueness/invertibility claim.
- Makes one missing bridge lemma explicit so obstruction is auditable.
-/

import Mathlib
import ToeFormal.Variational.ActionRep32CubicLane
import ToeFormal.Variational.GR01BridgePromotion
import ToeFormal.Variational.GR01Mainstream3DSpherical

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

/-!
Micro-lemma 1: explicit bridge sequence from finite-difference representability
to the action-variation bridge surface.
-/
theorem actionRep32_variation_bridge_sequence_discrete_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32) :
    ActionVariationBridgeRep32At ε hε := by
  have hfd :
      ActionRep32FiniteDifferenceRepresentsP ε hε :=
    ActionRep32FiniteDifferenceRepresentsP_cubic_of_RAC
      declared_g_rep32
      ε
      hε
      hAction
      hP
      hRAC
  have hEL :
      ActionRep32FiniteDifferenceRepresentsEL ε hε :=
    ActionRep32FiniteDifferenceRepresentsEL_of_rep32 ε hε hfd
  exact ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL ε hε hEL

theorem actionRep32_variation_bridge_sequence_from_algebraic_deviation_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε) :
    ActionVariationBridgeRep32At ε hε := by
  exact
    ActionVariationBridgeRep32At_cubic_of_deviationZeroAtStep
      declared_g_rep32
      ε
      hε
      hAction
      hP
      hDevZero

theorem actionRep32_variation_bridge_sequence_from_algebraic_deviation_default_binding_v0
    (ε : Real) (hε : ε ≠ 0)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε) :
    ActionVariationBridgeRep32At ε hε := by
  exact
    actionRep32_variation_bridge_sequence_from_algebraic_deviation_v0
      ε
      hε
      actionRep32_action_default_binding
      P_rep32_def
      hDevZero

def actionRep32_algebraic_deviation_surface_discrete_v0
    (g : ℂ)
    (ε : Real) : Prop :=
  ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
    formalFirstVariationRep32OpAt ε actionRep32.action δ ψ -
      pairingRep32' (P_rep32 ψ) (δ ψ) =
        cubicLinearDeviation g δ ψ +
          ε * cubicRemainder₂ g δ ψ +
          ε^2 * cubicRemainder₃ g δ ψ +
          ε^3 * cubicRemainder₄ g δ ψ

theorem actionRep32_variation_deviation_sequence_discrete_v0
    (g : ℂ)
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic g)
    (hP : P_rep32 = P_cubic_rep32_def g) :
    actionRep32_algebraic_deviation_surface_discrete_v0 g ε := by
  intro δ ψ
  exact
    ActionRep32FiniteDifferenceDeviationFromP_of_cubic
      g
      hAction
      hP
      ε
      hε
      δ
      ψ

theorem actionRep32_variation_deviation_sequence_discrete_default_binding_v0
    (ε : Real) (hε : ε ≠ 0) :
    actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε := by
  intro δ ψ
  exact
    ActionRep32FiniteDifferenceDeviationFromP_of_cubic
      declared_g_rep32
      actionRep32_action_default_binding
      P_rep32_def
      ε
      hε

theorem actionRep32_fd_deviation_with_Pcubic_from_algebraic_surface_v0
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε) :
    ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      formalFirstVariationRep32OpAt ε actionRep32.action δ ψ -
        pairingRep32' (P_cubic_rep32_def declared_g_rep32 ψ) (δ ψ) =
          cubicLinearDeviation declared_g_rep32 δ ψ +
            ε * cubicRemainder₂ declared_g_rep32 δ ψ +
            ε^2 * cubicRemainder₃ declared_g_rep32 δ ψ +
            ε^3 * cubicRemainder₄ declared_g_rep32 δ ψ := by
  intro δ ψ
  simpa [hP] using hDeviationSurface δ ψ

theorem actionRep32_cubic_deviation_collapse_from_vanishing_v0
    (ε : Real)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε) :
    ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      cubicLinearDeviation declared_g_rep32 δ ψ +
        ε * cubicRemainder₂ declared_g_rep32 δ ψ +
        ε^2 * cubicRemainder₃ declared_g_rep32 δ ψ +
        ε^3 * cubicRemainder₄ declared_g_rep32 δ ψ = 0 := by
  intro δ ψ
  have hTotalZero :
      cubicTotalDeviationAtStep declared_g_rep32 ε δ ψ = 0 :=
    hDevZero δ ψ
  simpa [cubicTotalDeviationAtStep] using hTotalZero

theorem actionRep32_fd_equals_Pcubic_from_algebraic_surface_and_vanishing_v0
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε) :
    ∀ (δ : FieldRep32 -> FieldRep32) (ψ : FieldRep32),
      formalFirstVariationRep32OpAt ε actionRep32.action δ ψ =
        pairingRep32' (P_cubic_rep32_def declared_g_rep32 ψ) (δ ψ) := by
  intro δ ψ
  have hDeviationWithPcubic :
      formalFirstVariationRep32OpAt ε actionRep32.action δ ψ -
        pairingRep32' (P_cubic_rep32_def declared_g_rep32 ψ) (δ ψ) =
          cubicLinearDeviation declared_g_rep32 δ ψ +
            ε * cubicRemainder₂ declared_g_rep32 δ ψ +
            ε^2 * cubicRemainder₃ declared_g_rep32 δ ψ +
            ε^3 * cubicRemainder₄ declared_g_rep32 δ ψ :=
    actionRep32_fd_deviation_with_Pcubic_from_algebraic_surface_v0
      ε
      hP
      hDeviationSurface
      δ
      ψ
  have hCollapsed :
      cubicLinearDeviation declared_g_rep32 δ ψ +
        ε * cubicRemainder₂ declared_g_rep32 δ ψ +
        ε^2 * cubicRemainder₃ declared_g_rep32 δ ψ +
        ε^3 * cubicRemainder₄ declared_g_rep32 δ ψ = 0 :=
    actionRep32_cubic_deviation_collapse_from_vanishing_v0
      ε
      hDevZero
      δ
      ψ
  have hZero :
      formalFirstVariationRep32OpAt ε actionRep32.action δ ψ -
        pairingRep32' (P_cubic_rep32_def declared_g_rep32 ψ) (δ ψ) = 0 := by
    simpa [hCollapsed] using hDeviationWithPcubic
  exact sub_eq_zero.mp hZero

/-!
Micro-lemma 2: EL identification from the pinned Rep32 cubic equality.
-/
theorem actionRep32_el_identification_discrete_v0
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  simpa [hP] using EL_toe_eq_P_rep32

/-!
Pinned minimal transport obligation (current obstruction):
- action-side variation bridge assembly is already discharged above.
- the remaining missing interface is EL-surface semantics to pointwise
  3D residual (away from source).
-/
def actionRep32_el_to_residual3d_away_from_source_transport_v0
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscretePoissonResidual3D Φ3D ρ3D κ p = 0

/-- Pinned interface: EL-surface semantics to radial residual semantics. -/
def actionRep32_el_to_radial_residual_transport_interface_v0
    (Φr ρr : RadialField)
    (κ : Real) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
    ∀ i : Int, DiscretePoissonResidualRadial Φr ρr κ i = 0

/-- Smaller interface token: EL-surface semantics to a radial evaluator zero condition. -/
def actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
    ∀ i : Int, evalRadial Φr ρr κ i = 0

/-- Interface token: evaluator agrees pointwise with the radial residual formula. -/
def actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real) : Prop :=
  ∀ i : Int, evalRadial Φr ρr κ i = DiscretePoissonResidualRadial Φr ρr κ i

/-- Concrete radial evaluator induced by the extracted radial operator surface. -/
def evalRadial_rep32_cubic
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (i : Int) : Real :=
  hLaplacianExtraction.extractedOperator Φr i - κ * ρr i

theorem evalRadial_rep32_cubic_matches_discrete_residual_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real) :
    actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  intro i
  have hExtracted :
      hLaplacianExtraction.extractedOperator Φr i = DiscreteLaplacian1D Φr i := by
    simpa using
      congrArg (fun op => op Φr i) hLaplacianExtraction.h_extracted_is_discrete
  dsimp [evalRadial_rep32_cubic, DiscretePoissonResidualRadial, DiscretePoissonResidual1D]
  simp [hExtracted]

/-- Action-native interface: FD expansion + remainder-vanishing yield evaluator transport. -/
def actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (ε : Real) : Prop :=
  actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε ->
    ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε ->
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ

/-- Probe-level interface: EL-core semantics force cubic pairing zero on designated probes. -/
def actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
    (probeVariation probeState : Int -> FieldRep32) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
    ∀ i : Int,
      pairingRep32'
        (P_cubic_rep32_def declared_g_rep32 (probeState i))
        (probeVariation i) = 0

/-- Probe-level interface: finite-difference observable realizes the target evaluator. -/
def actionRep32_probe_fd_matches_radial_evaluator_interface_v0
    (ε : Real)
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32) : Prop :=
  ∀ i : Int,
    formalFirstVariationRep32OpAt
        ε
        actionRep32.action
        (probeVariation i)
        (probeState i)
      = evalRadial Φr ρr κ i

def actionRep32_probe_pairing_matches_radial_evaluator_interface_v0
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32) : Prop :=
  ∀ i : Int,
    pairingRep32'
      (P_cubic_rep32_def declared_g_rep32 (probeState i))
      (probeVariation i) =
        evalRadial Φr ρr κ i

structure actionRep32_probe_pairing_to_radial_model_assumptions_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32) : Prop where
  pairing_zero :
    ∀ i : Int,
      pairingRep32'
        (P_cubic_rep32_def declared_g_rep32 (probeState i))
        (probeVariation i) = 0
  pairing_matches_eval :
    actionRep32_probe_pairing_matches_radial_evaluator_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ
      probeVariation
      probeState

def actionRep32_probe_pairing_model_package_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real) : Prop :=
  ∃ (δProbe ψProbe : Int -> FieldRep32),
    actionRep32_probe_pairing_to_radial_model_assumptions_v0
      hLaplacianExtraction
      Φr
      ρr
      κ
      δProbe
      ψProbe

theorem actionRep32_probe_pairing_matches_radial_evaluator_from_model_assumptions_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeModel :
      actionRep32_probe_pairing_to_radial_model_assumptions_v0
        hLaplacianExtraction
        Φr
        ρr
        κ
        probeVariation
        probeState) :
    actionRep32_probe_pairing_matches_radial_evaluator_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ
      probeVariation
      probeState :=
  hProbeModel.pairing_matches_eval

theorem actionRep32_probe_fd_matches_radial_evaluator_from_pairing_and_fd_expansion_v0
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbePairingMatchesEvaluator :
      actionRep32_probe_pairing_matches_radial_evaluator_interface_v0
        evalRadial
        Φr
        ρr
        κ
        probeVariation
        probeState) :
    actionRep32_probe_fd_matches_radial_evaluator_interface_v0
      ε
      evalRadial
      Φr
      ρr
      κ
      probeVariation
      probeState := by
  intro i
  calc
    formalFirstVariationRep32OpAt
        ε
        actionRep32.action
        (probeVariation i)
        (probeState i)
        =
        pairingRep32'
          (P_cubic_rep32_def declared_g_rep32 (probeState i))
          (probeVariation i) :=
      actionRep32_fd_equals_Pcubic_from_algebraic_surface_and_vanishing_v0
        ε
        hP
        hDeviationSurface
        hDevZero
        (probeVariation i)
        (probeState i)
    _ = evalRadial Φr ρr κ i := hProbePairingMatchesEvaluator i

theorem actionRep32_el_to_radial_evaluator_zero_from_fd_expansion_and_probe_interfaces_v0
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        evalRadial
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      evalRadial
      Φr
      ρr
      κ := by
  intro hEL i
  have hFdEqPcubicOnProbe :
      formalFirstVariationRep32OpAt
          ε
          actionRep32.action
          (probeVariation i)
          (probeState i)
        =
        pairingRep32'
          (P_cubic_rep32_def declared_g_rep32 (probeState i))
          (probeVariation i) :=
    actionRep32_fd_equals_Pcubic_from_algebraic_surface_and_vanishing_v0
      ε
      hP
      hDeviationSurface
      hDevZero
      (probeVariation i)
      (probeState i)
  have hPairingZeroOnProbe :
      pairingRep32'
        (P_cubic_rep32_def declared_g_rep32 (probeState i))
        (probeVariation i) = 0 :=
    hELCoreImpliesProbePairingZero hEL i
  have hFDZeroOnProbe :
      formalFirstVariationRep32OpAt
          ε
          actionRep32.action
          (probeVariation i)
          (probeState i) = 0 := by
    calc
      formalFirstVariationRep32OpAt
          ε
          actionRep32.action
          (probeVariation i)
          (probeState i)
          =
          pairingRep32'
            (P_cubic_rep32_def declared_g_rep32 (probeState i))
            (probeVariation i) := hFdEqPcubicOnProbe
      _ = 0 := hPairingZeroOnProbe
  have hEvalEqFD :
      formalFirstVariationRep32OpAt
          ε
          actionRep32.action
          (probeVariation i)
          (probeState i)
        =
        evalRadial Φr ρr κ i :=
    hProbeFDMatchesEvaluator i
  calc
    evalRadial Φr ρr κ i
        =
        formalFirstVariationRep32OpAt
          ε
          actionRep32.action
          (probeVariation i)
          (probeState i) := by
            symm
            exact hEvalEqFD
    _ = 0 := hFDZeroOnProbe

theorem actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_constructor_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState) :
    actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0
      hLaplacianExtraction
      Φr
      ρr
      κ
      ε := by
  intro hDeviationSurface hDevZero
  exact
    actionRep32_el_to_radial_evaluator_zero_from_fd_expansion_and_probe_interfaces_v0
      ε
      hP
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ
      probeVariation
      probeState
      hDeviationSurface
      hDevZero
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero

/-- Canonical probe variation for restricted evaluator slice: identically zero. -/
def actionRep32_probeVariation_zero_v0 : Int -> FieldRep32 -> FieldRep32 :=
  fun _ _ => 0

/-- Canonical probe state for restricted evaluator slice: identically zero. -/
def actionRep32_probeState_zero_v0 : Int -> FieldRep32 :=
  fun _ => 0

/-- Restricted evaluator slice induced directly by finite-difference probes. -/
def evalRadial_from_probe_fd_v0
    (ε : Real)
    (probeVariation : Int -> FieldRep32 -> FieldRep32)
    (probeState : Int -> FieldRep32)
    (_Φr _ρr : RadialField)
    (_κ : Real)
    (i : Int) : Real :=
  formalFirstVariationRep32OpAt
    ε
    actionRep32.action
    (probeVariation i)
    (probeState i)

/-- Restricted evaluator slice specialized to canonical zero probes. -/
def evalRadial_from_zero_probe_fd_v0
    (ε : Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (i : Int) : Real :=
  evalRadial_from_probe_fd_v0
    ε
    actionRep32_probeVariation_zero_v0
    actionRep32_probeState_zero_v0
    Φr
    ρr
    κ
    i

theorem actionRep32_probe_fd_matches_evalRadial_from_probe_fd_v0
    (ε : Real)
    (probeVariation : Int -> FieldRep32 -> FieldRep32)
    (probeState : Int -> FieldRep32)
    (Φr ρr : RadialField)
    (κ : Real) :
    actionRep32_probe_fd_matches_radial_evaluator_interface_v0
      ε
      (evalRadial_from_probe_fd_v0 ε probeVariation probeState)
      Φr
      ρr
      κ
      probeVariation
      probeState := by
  intro i
  rfl

theorem actionRep32_el_core_implies_probe_pcubic_pairing_zero_of_zero_probe_v0 :
    actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
      actionRep32_probeVariation_zero_v0
      actionRep32_probeState_zero_v0 := by
  intro _hEL i
  simp [actionRep32_probeVariation_zero_v0, actionRep32_probeState_zero_v0]

theorem actionRep32_el_to_zero_probe_evaluator_zero_from_fd_expansion_v0
    (ε : Real)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (Φr ρr : RadialField)
    (κ : Real)
    (hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_from_zero_probe_fd_v0 ε)
      Φr
      ρr
      κ := by
  have hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_from_zero_probe_fd_v0 ε)
        Φr
        ρr
        κ
        actionRep32_probeVariation_zero_v0
        actionRep32_probeState_zero_v0 :=
    actionRep32_probe_fd_matches_evalRadial_from_probe_fd_v0
      ε
      actionRep32_probeVariation_zero_v0
      actionRep32_probeState_zero_v0
      Φr
      ρr
      κ
  exact
    actionRep32_el_to_radial_evaluator_zero_from_fd_expansion_and_probe_interfaces_v0
      ε
      hP
      (evalRadial_from_zero_probe_fd_v0 ε)
      Φr
      ρr
      κ
      actionRep32_probeVariation_zero_v0
      actionRep32_probeState_zero_v0
      hDeviationSurface
      hDevZero
      hProbeFDMatchesEvaluator
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_of_zero_probe_v0

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (hEvalFromFDExpansionAndVanishing :
      actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0
        hLaplacianExtraction
        Φr
        ρr
        κ
        ε) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  have hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε :=
    actionRep32_variation_deviation_sequence_discrete_v0
      declared_g_rep32
      ε
      hε
      hAction
      hP
  exact hEvalFromFDExpansionAndVanishing hDeviationSurface hDevZero

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_probe_interfaces_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  have hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε :=
    actionRep32_variation_deviation_sequence_discrete_v0
      declared_g_rep32
      ε
      hε
      hAction
      hP
  exact
    actionRep32_el_to_radial_evaluator_zero_from_fd_expansion_and_probe_interfaces_v0
      ε
      hP
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ
      probeVariation
      probeState
      hDeviationSurface
      hDevZero
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  exact
    actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_probe_interfaces_v0
      ε
      hε
      hAction
      hP
      hDevZero
      hLaplacianExtraction
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hLaplacianExtraction : LaplacianExtraction)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbePairingModel :
      actionRep32_probe_pairing_to_radial_model_assumptions_v0
        hLaplacianExtraction
        Φr
        ρr
        κ
        probeVariation
        probeState) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  have hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState := by
    intro _hEL i
    exact hProbePairingModel.pairing_zero i
  have hDevZero :
      ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε :=
    ActionRep32CubicDeviationZeroAtStep_of_RAC
      declared_g_rep32
      ε
      hRAC
  have hDeviationSurface :
      actionRep32_algebraic_deviation_surface_discrete_v0 declared_g_rep32 ε :=
    actionRep32_variation_deviation_sequence_discrete_default_binding_v0
      ε
      hε
  have hProbePairingMatchesEvaluator :
      actionRep32_probe_pairing_matches_radial_evaluator_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState :=
    actionRep32_probe_pairing_matches_radial_evaluator_from_model_assumptions_v0
      hLaplacianExtraction
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbePairingModel
  have hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState :=
    actionRep32_probe_fd_matches_radial_evaluator_from_pairing_and_fd_expansion_v0
      ε
      P_rep32_def
      hDeviationSurface
      hDevZero
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbePairingMatchesEvaluator
  exact
    actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_v0
      ε
      hε
      actionRep32_action_default_binding
      P_rep32_def
      hDevZero
      hLaplacianExtraction
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero

theorem mk_ELImpliesDiscretePoissonResidual_from_bridge_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ELImpliesDiscretePoissonResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  refine ⟨?_⟩
  intro hEL i
  have hResidualFromCore :
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i -
          hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0 :=
    gr01_operator_residual_from_bound_bridge_assumptions
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
      hEL
  exact
    OperatorToDiscreteResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hResidualFromCore
      i

theorem actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  intro hELCore i
  have hEvalZero :
      evalRadial_rep32_cubic hLaplacianExtraction Φr ρr κ i = 0 :=
    hELToEvalZero hELCore i
  simpa [evalRadial_rep32_cubic, hΦ, hρ, hκ] using hEvalZero

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (hEvalFromFDExpansionAndVanishing :
      actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0
        hLaplacianExtraction
        Φr
        ρr
        κ
        ε)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0
      ε
      hε
      hAction
      hP
      hDevZero
      hLaplacianExtraction
      Φr
      ρr
      κ
      hEvalFromFDExpansionAndVanishing
  exact
    actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      hELToEvalZero
      hΦ
      hρ
      hκ

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_and_probe_interfaces_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_probe_interfaces_v0
      ε
      hε
      hAction
      hP
      hDevZero
      hLaplacianExtraction
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero
  exact
    actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      hELToEvalZero
      hΦ
      hρ
      hκ

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  exact
    actionRep32_el_implies_operator_residual_transport_from_fd_expansion_and_probe_interfaces_v0
      ε
      hε
      hAction
      hP
      hDevZero
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero
      hΦ
      hρ
      hκ

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (probeVariation probeState : Int -> FieldRep32)
    (hProbeFDMatchesEvaluator :
      actionRep32_probe_fd_matches_radial_evaluator_interface_v0
        ε
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ
        probeVariation
        probeState)
    (hELCoreImpliesProbePairingZero :
      actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0
        probeVariation
        probeState)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  have hDevZero :
      ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε :=
    ActionRep32CubicDeviationZeroAtStep_of_RAC
      declared_g_rep32
      ε
      hRAC
  exact
    actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0
      ε
      hε
      hAction
      hP
      hDevZero
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      probeVariation
      probeState
      hProbeFDMatchesEvaluator
      hELCoreImpliesProbePairingZero
      hΦ
      hρ
      hκ

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  let _ := actionRep32_action_default_binding
  let _ := P_rep32_def
  let _ := hRAC
  let _ := hε
  let _ := ε
  exact
    actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ
      hELToEvalZero
      rfl
      rfl
      rfl

theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProbePairingModelPackage :
      actionRep32_probe_pairing_model_package_v0
        hLaplacianExtraction
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  rcases hProbePairingModelPackage with ⟨δProbe, ψProbe, hProbePairingModel⟩
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0
      ε
      hε
      hRAC
      hLaplacianExtraction
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ
      δProbe
      ψProbe
      hProbePairingModel
  exact
    actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ
      hELToEvalZero
      rfl
      rfl
      rfl

theorem actionRep32_operator_residual_under_bound_from_radial_evaluator_interface_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (phiBound rhoBound : Real)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound := by
  have hTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      hELToEvalZero
      hΦ
      hρ
      hκ
  exact
    gr01_operator_residual_under_bound_from_transport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hTransport

theorem actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration :=
  gr01_operator_residual_transport_from_bound_bridge_assumptions
    hPotentialIdentification
    hSourceIdentification
    hLaplacianExtraction
    hUnitsAndCalibration
    phiBound
    rhoBound
    hWeakFieldUniformBound
    hELImpliesOperatorResidualUnderBound

theorem actionRep32_el_core_equals_pcubic_from_cubic_lane_default_binding_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  have hLane :=
    Rep32_cubic_lane_default_binding
      ε
      hε
      hRAC
  exact hLane.2

theorem actionRep32_el_core_equals_pcubic_from_action_binding_and_rac_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32) :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
  exact
    EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions
      ε
      hε
      actionRep32_action_default_binding
      hRAC

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_without_hP_premise_v0
    (ε : Real) (hε : ε ≠ 0)
  (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  have hProjectionFromCore :
      WeakFieldProjectionFromCore
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mkWeakFieldProjectionFromCore
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual
  let _ := ε
  let _ := hε
  have hELCore :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
    exact
      EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions
        ε
        hε
        actionRep32_action_default_binding
        hRAC
  have hResidual :
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    weakFieldResidualFromProjection
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionFromCore
      hELCore
  let _ := hWeakFieldAnsatz
  let _ := hSmallPerturbationExpansion
  let _ := hUnitsAndCalibration.h_kappa_relation
  refine ⟨hPotentialIdentification.Φ, hSourceIdentification.ρ, hUnitsAndCalibration.κ, ?_⟩
  intro i
  exact hResidual i

theorem actionRep32_weak_field_poisson_limit_from_operator_transport_compat_core_v0
    (ε : Real) (hε : ε ≠ 0)
  (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration := by
    refine ⟨?_⟩
    intro hELCore i
    have hResidualFromCore :
        ∀ j : Int,
          hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ j
            - hUnitsAndCalibration.κ * hSourceIdentification.ρ j = 0 :=
      hOperatorTransport hELCore
    exact
      OperatorToDiscreteResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        hResidualFromCore
        i
  have hProjectionFromCore :
      WeakFieldProjectionFromCore
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mkWeakFieldProjectionFromCore
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual
  let _ := ε
  let _ := hε
  have hELCore :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
    exact
      EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions
        ε
        hε
        actionRep32_action_default_binding
        hRAC
  have hResidual :
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    weakFieldResidualFromProjection
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionFromCore
      hELCore
  let _ := hWeakFieldAnsatz
  let _ := hSmallPerturbationExpansion
  let _ := hUnitsAndCalibration.h_kappa_relation
  refine ⟨hPotentialIdentification.Φ, hSourceIdentification.ρ, hUnitsAndCalibration.κ, ?_⟩
  intro i
  exact hResidual i

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := P_rep32_def
  have hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification :=
    gr01_projection_map_well_formed_from_uniform_bound_v0
      hPotentialIdentification
      hSourceIdentification
      phiBound
      rhoBound
      hWeakFieldUniformBound
  have hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion :=
    weakFieldTruncationSound_default_v0
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
  exact
    actionRep32_weak_field_poisson_limit_from_operator_transport_compat_core_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_from_operator_transport_core_v0
    (ε : Real) (hε : ε ≠ 0)
  (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration := by
    refine ⟨?_⟩
    intro hELCore i
    have hResidualFromCore :
        ∀ j : Int,
          hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ j
            - hUnitsAndCalibration.κ * hSourceIdentification.ρ j = 0 :=
      hOperatorTransport hELCore
    exact
      OperatorToDiscreteResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        hResidualFromCore
        i
  have hProjectionFromCore :
      WeakFieldProjectionFromCore
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mkWeakFieldProjectionFromCore
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual
  let _ := ε
  let _ := hε
  have hELCore :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
    exact
      EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions
        ε
        hε
        actionRep32_action_default_binding
        hRAC
  have hResidual :
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    weakFieldResidualFromProjection
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionFromCore
      hELCore
  let _ := hWeakFieldAnsatz
  let _ := hSmallPerturbationExpansion
  let _ := hUnitsAndCalibration.h_kappa_relation
  refine ⟨hPotentialIdentification.Φ, hSourceIdentification.ρ, hUnitsAndCalibration.κ, ?_⟩
  intro i
  exact hResidual i

theorem actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := actionRep32_action_default_binding
  let _ := P_rep32_def
  have hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification :=
    gr01_projection_map_well_formed_from_uniform_bound_v0
      hPotentialIdentification
      hSourceIdentification
      phiBound
      rhoBound
      hWeakFieldUniformBound
  have hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion :=
    weakFieldTruncationSound_default_v0
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
  exact
    actionRep32_weak_field_poisson_limit_from_operator_transport_core_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (hEvalFromFDExpansionAndVanishing :
      actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0
        hLaplacianExtraction
        Φr
        ρr
        κ
        ε)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound) :
    WeakFieldPoissonLimitStatement := by
  have hDevZero :
      ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε :=
    ActionRep32CubicDeviationZeroAtStep_of_RAC
      declared_g_rep32
      ε
      hRAC
  have hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0
      ε
      hε
      actionRep32_action_default_binding
      P_rep32_def
      hDevZero
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      Φr
      ρr
      κ
      hEvalFromFDExpansionAndVanishing
      hΦ
      hρ
      hκ
  exact
    actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_under_action_native_transport_constructor_shared_core_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ)
    (hClose :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration ->
      WeakFieldPoissonLimitStatement) :
    WeakFieldPoissonLimitStatement := by
  have hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0
      ε
      hε
      hRAC
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hELToEvalZero
  exact hClose hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0
  let _ := actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0
  exact
    actionRep32_weak_field_poisson_limit_under_action_native_transport_constructor_shared_core_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hELToEvalZero
      (fun hOperatorTransport =>
        actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0
          ε
          hε
          hRAC
          hWeakFieldAnsatz
          hSmallPerturbationExpansion
          hPotentialIdentification
          hSourceIdentification
          hLaplacianExtraction
          hUnitsAndCalibration
          phiBound
          rhoBound
          hWeakFieldUniformBound
          hOperatorTransport)

theorem actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProbePairingModelPackage :
      actionRep32_probe_pairing_model_package_v0
        hLaplacianExtraction
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0
  let _ := actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0
  have hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0
      ε
      hε
      hRAC
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hProbePairingModelPackage
  exact
    actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  exact
    actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hOperatorTransport

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0
  let _ := actionRep32_el_to_evalRadial_rep32_cubic_zero_of_bridge_v0
  let _ := actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_of_bridge_v0
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ
      rfl
      rfl
      rfl
  exact
    actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ
      hELToEvalZero
      rfl
      rfl
      rfl
      phiBound
      rhoBound
      hWeakFieldUniformBound

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_of_el_semantics_v0
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  intro hEL i
  have hResidual :
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ
        i = 0 :=
    hELImpliesDiscretePoissonResidual.el_implies_discrete_residual hEL i
  have hExtracted :
      hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i =
        DiscreteLaplacian1D hPotentialIdentification.Φ i := by
    simpa using
      congrArg
        (fun op => op hPotentialIdentification.Φ i)
        hLaplacianExtraction.h_extracted_is_discrete
  have hResidualCanonical :
      DiscreteLaplacian1D hPotentialIdentification.Φ i -
        hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0 := by
    simpa [DiscretePoissonResidual1D] using hResidual
  have hEvalAtBase :
      evalRadial_rep32_cubic
          hLaplacianExtraction
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ
          i = 0 := by
    calc
      evalRadial_rep32_cubic
          hLaplacianExtraction
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ
          i
          =
          hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i -
            hUnitsAndCalibration.κ * hSourceIdentification.ρ i := by
            rfl
      _ = DiscreteLaplacian1D hPotentialIdentification.Φ i -
            hUnitsAndCalibration.κ * hSourceIdentification.ρ i := by
            simp [hExtracted]
      _ = 0 := hResidualCanonical
  simpa [hΦ, hρ, hκ] using hEvalAtBase

theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_of_bridge_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (Φr ρr : RadialField)
    (κ : Real)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ) :
    actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      Φr
      ρr
      κ := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mk_ELImpliesDiscretePoissonResidual_from_bridge_v0
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
  exact actionRep32_el_to_evalRadial_rep32_cubic_zero_of_el_semantics_v0
    hLaplacianExtraction
    hPotentialIdentification
    hSourceIdentification
    hUnitsAndCalibration
    hELImpliesDiscretePoissonResidual
    Φr
    ρr
    κ
    hΦ
    hρ
    hκ

theorem actionRep32_el_to_radial_residual_transport_of_evaluator_interfaces_v0
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (Φr ρr : RadialField)
    (κ : Real)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        evalRadial
        Φr
        ρr
        κ)
    (hEvalMatchesResidual :
      actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
        evalRadial
        Φr
        ρr
        κ) :
    actionRep32_el_to_radial_residual_transport_interface_v0 Φr ρr κ := by
  intro hEL i
  have hEvalZero : evalRadial Φr ρr κ i = 0 := hELToEvalZero hEL i
  have hMatch :
      evalRadial Φr ρr κ i = DiscretePoissonResidualRadial Φr ρr κ i :=
    hEvalMatchesResidual i
  simpa [hMatch] using hEvalZero

theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (Φr ρr : RadialField)
    (κ : Real)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        Φr
        ρr
        κ)
    (hΦ : hPotentialIdentification.Φ = Φr)
    (hρ : hSourceIdentification.ρ = ρr)
    (hκ : hUnitsAndCalibration.κ = κ)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := phiBound
  let _ := rhoBound
  let _ := hWeakFieldUniformBound
  let _ := actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0
  have hELToEvalZeroAtIdent :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ := by
    intro hELCore i
    have hEvalZero :
        evalRadial_rep32_cubic hLaplacianExtraction Φr ρr κ i = 0 :=
      hELToEvalZero hELCore i
    simpa [hΦ, hρ, hκ] using hEvalZero
  exact
    actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0
      ε
      hε
      hRAC
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hELToEvalZeroAtIdent
      phiBound
      rhoBound
      hWeakFieldUniformBound

/-- Compatibility token (derived from EL→residual transport + residual algebra). -/
def actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p

theorem actionRep32_el_to_residual3d_away_from_source_of_radial_interface_v0
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (hELToRadialResidual :
      actionRep32_el_to_radial_residual_transport_interface_v0
        hMapping.Φradial
        hMapping.ρradial
        κ) :
    actionRep32_el_to_residual3d_away_from_source_transport_v0
      hMapping.Φ3D
      hMapping.ρ3D
      κ
      hMapping.radialIndex
      sourceIndex := by
  intro hEL p hpNotSource
  let _ := hpNotSource
  have hResidualReduction :
      DiscretePoissonResidual3D hMapping.Φ3D hMapping.ρ3D κ p =
        DiscretePoissonResidualRadial
          hMapping.Φradial
          hMapping.ρradial
          κ
          (hMapping.radialIndex p) :=
    gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry
      hMapping
      κ
      p
  have hRadialResidual :
      DiscretePoissonResidualRadial
        hMapping.Φradial
        hMapping.ρradial
        κ
        (hMapping.radialIndex p) = 0 :=
    hELToRadialResidual hEL (hMapping.radialIndex p)
  exact hResidualReduction.trans hRadialResidual

/-!
Micro-transport B (discharged):
pointwise residual zero implies operator equation at the same point.
-/
theorem actionRep32_residual3d_away_from_source_implies_operator_equation_discrete_v0
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hResidualAway :
      ∀ p : LatticePoint3D,
        radialIndex p ≠ sourceIndex ->
          DiscretePoissonResidual3D Φ3D ρ3D κ p = 0) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  intro p hpNotSource
  have hResidualZero :
      DiscretePoissonResidual3D Φ3D ρ3D κ p = 0 :=
    hResidualAway p hpNotSource
  dsimp [DiscretePoissonResidual3D] at hResidualZero
  linarith

theorem actionRep32_el_to_operator_equation_3d_away_from_source_of_el_to_residual_transport_v0
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hELToResidual :
      actionRep32_el_to_residual3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
      Φ3D ρ3D κ radialIndex sourceIndex := by
  intro hEL
  have hResidualAway :
      ∀ p : LatticePoint3D,
        radialIndex p ≠ sourceIndex ->
          DiscretePoissonResidual3D Φ3D ρ3D κ p = 0 :=
    hELToResidual hEL
  exact
    actionRep32_residual3d_away_from_source_implies_operator_equation_discrete_v0
      Φ3D ρ3D κ radialIndex sourceIndex hResidualAway

/-- Compatibility wrapper preserving the prior bridge-shaped token. -/
def actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
    (ε : Real) (hε : ε ≠ 0)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int) : Prop :=
  ActionVariationBridgeRep32At ε hε ->
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 ->
      ∀ p : LatticePoint3D,
        radialIndex p ≠ sourceIndex ->
          DiscreteLaplacian3D Φ3D p = κ * ρ3D p

theorem actionRep32_bridge_to_operator_equation_3d_away_from_source_of_transport_v0
    (ε : Real) (hε : ε ≠ 0)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hTransport :
      actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
      ε hε Φ3D ρ3D κ radialIndex sourceIndex := by
  intro _hBridge hEL p hpNotSource
  exact hTransport hEL p hpNotSource

/-!
Requested theorem-surface token:
- assembles the proved action-side sequence and isolates the final missing
  bridge as an explicit argument.
-/
theorem actionRep32_produces_operator_equation_discrete_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hBridgeToOperator :
      actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
        ε hε Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hBridge :
      ActionVariationBridgeRep32At ε hε :=
    actionRep32_variation_bridge_sequence_discrete_v0 ε hε hAction hP hRAC
  have hEL :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 :=
    actionRep32_el_identification_discrete_v0 hP
  exact hBridgeToOperator hBridge hEL

theorem actionRep32_produces_operator_equation_discrete_of_transport_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hTransport :
      actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hBridgeToOperator :
      actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
        ε hε Φ3D ρ3D κ radialIndex sourceIndex :=
    actionRep32_bridge_to_operator_equation_3d_away_from_source_of_transport_v0
      ε hε Φ3D ρ3D κ radialIndex sourceIndex hTransport
  exact actionRep32_produces_operator_equation_discrete_v0
    ε hε hAction hP hRAC Φ3D ρ3D κ radialIndex sourceIndex hBridgeToOperator

theorem actionRep32_produces_operator_equation_discrete_from_algebraic_deviation_v0
    (ε : Real) (hε : ε ≠ 0)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hBridgeToOperator :
      actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
        ε hε Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hBridge :
      ActionVariationBridgeRep32At ε hε :=
    actionRep32_variation_bridge_sequence_from_algebraic_deviation_default_binding_v0
      ε
      hε
      hDevZero
  have hEL :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 :=
    actionRep32_el_identification_discrete_v0 P_rep32_def
  intro p hpNotSource
  exact hBridgeToOperator hBridge hEL p hpNotSource

theorem actionRep32_produces_operator_equation_discrete_of_transport_from_algebraic_deviation_v0
    (ε : Real) (hε : ε ≠ 0)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hTransport :
      actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hBridgeToOperator :
      actionRep32_bridge_to_operator_equation_3d_away_from_source_v0
        ε hε Φ3D ρ3D κ radialIndex sourceIndex :=
    actionRep32_bridge_to_operator_equation_3d_away_from_source_of_transport_v0
      ε hε Φ3D ρ3D κ radialIndex sourceIndex hTransport
  exact
    actionRep32_produces_operator_equation_discrete_from_algebraic_deviation_v0
      ε
      hε
      hDevZero
      Φ3D
      ρ3D
      κ
      radialIndex
      sourceIndex
      hBridgeToOperator

/-!
Guarded route (anti-repackaging):
- no direct operator-equation assumption appears in the theorem signature.
- the only missing assumption is EL→residual transport.
-/
theorem actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hELToResidual :
      actionRep32_el_to_residual3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hTransport :
      actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex :=
    actionRep32_el_to_operator_equation_3d_away_from_source_of_el_to_residual_transport_v0
      Φ3D ρ3D κ radialIndex sourceIndex hELToResidual
  exact actionRep32_produces_operator_equation_discrete_of_transport_v0
    ε hε hAction hP hRAC Φ3D ρ3D κ radialIndex sourceIndex hTransport

theorem actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_from_algebraic_deviation_v0
    (ε : Real) (hε : ε ≠ 0)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (Φ3D ρ3D : ScalarField3D)
    (κ : Real)
    (radialIndex : LatticePoint3D -> Int)
    (sourceIndex : Int)
    (hELToResidual :
      actionRep32_el_to_residual3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex) :
    ∀ p : LatticePoint3D,
      radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D Φ3D p = κ * ρ3D p := by
  have hTransport :
      actionRep32_el_to_operator_equation_3d_away_from_source_transport_v0
        Φ3D ρ3D κ radialIndex sourceIndex :=
    actionRep32_el_to_operator_equation_3d_away_from_source_of_el_to_residual_transport_v0
      Φ3D ρ3D κ radialIndex sourceIndex hELToResidual
  exact
    actionRep32_produces_operator_equation_discrete_of_transport_from_algebraic_deviation_v0
      ε
      hε
      hDevZero
      Φ3D
      ρ3D
      κ
      radialIndex
      sourceIndex
      hTransport

theorem actionRep32_produces_operator_equation_discrete_of_radial_interface_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (hELToRadialResidual :
      actionRep32_el_to_radial_residual_transport_interface_v0
        hMapping.Φradial
        hMapping.ρradial
        κ) :
    ∀ p : LatticePoint3D,
      hMapping.radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D hMapping.Φ3D p = κ * hMapping.ρ3D p := by
  have hELToResidual3D :
      actionRep32_el_to_residual3d_away_from_source_transport_v0
        hMapping.Φ3D
        hMapping.ρ3D
        κ
        hMapping.radialIndex
        sourceIndex :=
    actionRep32_el_to_residual3d_away_from_source_of_radial_interface_v0
      hMapping
      κ
      sourceIndex
      hELToRadialResidual
  exact actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_v0
    ε
    hε
    hAction
    hP
    hRAC
    hMapping.Φ3D
    hMapping.ρ3D
    κ
    hMapping.radialIndex
    sourceIndex
    hELToResidual3D

theorem actionRep32_produces_operator_equation_discrete_of_evaluator_interfaces_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (evalRadial : RadialField -> RadialField -> Real -> Int -> Real)
    (hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        evalRadial
        hMapping.Φradial
        hMapping.ρradial
        κ)
    (hEvalMatchesResidual :
      actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
        evalRadial
        hMapping.Φradial
        hMapping.ρradial
        κ) :
    ∀ p : LatticePoint3D,
      hMapping.radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D hMapping.Φ3D p = κ * hMapping.ρ3D p := by
  have hELToRadialResidual :
      actionRep32_el_to_radial_residual_transport_interface_v0
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    actionRep32_el_to_radial_residual_transport_of_evaluator_interfaces_v0
      evalRadial
      hMapping.Φradial
      hMapping.ρradial
      κ
      hELToEvalZero
      hEvalMatchesResidual
  exact actionRep32_produces_operator_equation_discrete_of_radial_interface_v0
    ε
    hε
    hAction
    hP
    hRAC
    hMapping
    κ
    sourceIndex
    hELToRadialResidual

theorem actionRep32_produces_operator_equation_discrete_of_rep32_cubic_evaluator_semantics_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration)
    (hΦ : hPotentialIdentification.Φ = hMapping.Φradial)
    (hρ : hSourceIdentification.ρ = hMapping.ρradial)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ∀ p : LatticePoint3D,
      hMapping.radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D hMapping.Φ3D p = κ * hMapping.ρ3D p := by
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_of_el_semantics_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hELImpliesDiscretePoissonResidual
      hMapping.Φradial
      hMapping.ρradial
      κ
      hΦ
      hρ
      hκ
  have hEvalMatchesResidual :
      actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    evalRadial_rep32_cubic_matches_discrete_residual_v0
      hLaplacianExtraction
      hMapping.Φradial
      hMapping.ρradial
      κ
  exact actionRep32_produces_operator_equation_discrete_of_evaluator_interfaces_v0
    ε
    hε
    hAction
    hP
    hRAC
    hMapping
    κ
    sourceIndex
    (evalRadial_rep32_cubic hLaplacianExtraction)
    hELToEvalZero
    hEvalMatchesResidual

theorem actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_v0
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hRAC : RAC_Rep32_Cubic declared_g_rep32)
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (hΦ : hPotentialIdentification.Φ = hMapping.Φradial)
    (hρ : hSourceIdentification.ρ = hMapping.ρradial)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ∀ p : LatticePoint3D,
      hMapping.radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D hMapping.Φ3D p = κ * hMapping.ρ3D p := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mk_ELImpliesDiscretePoissonResidual_from_bridge_v0
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
  exact actionRep32_produces_operator_equation_discrete_of_rep32_cubic_evaluator_semantics_v0
    ε
    hε
    hAction
    hP
    hRAC
    hMapping
    κ
    sourceIndex
    hLaplacianExtraction
    hPotentialIdentification
    hSourceIdentification
    hUnitsAndCalibration
    hELImpliesDiscretePoissonResidual
    hΦ
    hρ
    hκ

theorem actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_from_algebraic_deviation_v0
    (ε : Real) (hε : ε ≠ 0)
    (hDevZero : ActionRep32CubicDeviationZeroAtStep declared_g_rep32 ε)
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (sourceIndex : Int)
    (hLaplacianExtraction : LaplacianExtraction)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (hΦ : hPotentialIdentification.Φ = hMapping.Φradial)
    (hρ : hSourceIdentification.ρ = hMapping.ρradial)
    (hκ : hUnitsAndCalibration.κ = κ) :
    ∀ p : LatticePoint3D,
      hMapping.radialIndex p ≠ sourceIndex ->
        DiscreteLaplacian3D hMapping.Φ3D p = κ * hMapping.ρ3D p := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mk_ELImpliesDiscretePoissonResidual_from_bridge_v0
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
  have hELToEvalZero :
      actionRep32_el_to_radial_evaluator_zero_transport_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    actionRep32_el_to_evalRadial_rep32_cubic_zero_of_el_semantics_v0
      hLaplacianExtraction
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      hELImpliesDiscretePoissonResidual
      hMapping.Φradial
      hMapping.ρradial
      κ
      hΦ
      hρ
      hκ
  have hEvalMatchesResidual :
      actionRep32_radial_evaluator_matches_discrete_residual_interface_v0
        (evalRadial_rep32_cubic hLaplacianExtraction)
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    evalRadial_rep32_cubic_matches_discrete_residual_v0
      hLaplacianExtraction
      hMapping.Φradial
      hMapping.ρradial
      κ
  have hELToRadialResidual :
      actionRep32_el_to_radial_residual_transport_interface_v0
        hMapping.Φradial
        hMapping.ρradial
        κ :=
    actionRep32_el_to_radial_residual_transport_of_evaluator_interfaces_v0
      (evalRadial_rep32_cubic hLaplacianExtraction)
      hMapping.Φradial
      hMapping.ρradial
      κ
      hELToEvalZero
      hEvalMatchesResidual
  have hELToResidual3D :
      actionRep32_el_to_residual3d_away_from_source_transport_v0
        hMapping.Φ3D
        hMapping.ρ3D
        κ
        hMapping.radialIndex
        sourceIndex :=
    actionRep32_el_to_residual3d_away_from_source_of_radial_interface_v0
      hMapping
      κ
      sourceIndex
      hELToRadialResidual
  exact
    actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_from_algebraic_deviation_v0
      ε
      hε
      hDevZero
      hMapping.Φ3D
      hMapping.ρ3D
      κ
      hMapping.radialIndex
      sourceIndex
      hELToResidual3D

end

end Variational
end ToeFormal
