/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianQuadraticConsistency.lean

Theorem-facing A1A successor for the graph-Laplacian to continuum-Laplacian
channel.

Scope:
- prove a concrete centered three-point stencil consistency theorem for
  quadratic samples
- record the concrete obstruction preventing this toy theorem from closing the
  full A2A15A1A graph-Laplacian-to-continuum-Laplacian channel
- comply with the post-capstone anti-loop rule by proving a local channel
  consistency fact and recording an obstruction, not by adding a child split
- keep full analytic convergence, general function-space semantics, continuum
  Laplacian construction, Phase 2 authorization, seam closure, empirical
  validation, and master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialAnalyticIntervalLiftAssembly

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianQuadraticConsistency

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the theorem-facing A1A quadratic-stencil attempt. -/
def phase1Blocker003A2A15A1AQuadraticStencilConsistencyRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A_QUADRATIC_STENCIL_CONSISTENCY_" ++
    "PROVED_FULL_CHANNEL_RETAINED"

/-- Outcome id for the A1A theorem-facing successor. -/
def graphLaplacianQuadraticConsistencyOutcomeId : String :=
  "A2A15A1A_QUADRATIC_STENCIL_CONSISTENCY_PROVED_CONCRETE_" ++
    "OBSTRUCTION_RECORDED"

/-- Minimal three-point stencil around an interior point. -/
inductive ThreePointStencil where
  | left
  | center
  | right
deriving DecidableEq, Repr

instance : Inhabited ThreePointStencil where
  default := ThreePointStencil.center

/-- Coordinates of the symmetric three-point stencil. -/
def threePointCoordinate (h : Real) : ThreePointStencil -> Real
  | .left => -h
  | .center => 0
  | .right => h

/-- Quadratic field sampled on the three-point stencil. -/
def sampledQuadraticField (a b c h : Real) :
    ContinuumField ThreePointStencil :=
  fun p =>
    let x := threePointCoordinate h p
    a * x * x + b * x + c

/-- Unscaled centered graph-Laplacian numerator at the center point. -/
def centeredGraphLaplacianNumerator
    (f : ContinuumField ThreePointStencil) : Real :=
  f ThreePointStencil.left -
    2 * f ThreePointStencil.center +
    f ThreePointStencil.right

/-- Scaled centered graph-Laplacian at the center point. -/
def centeredScaledGraphLaplacianAtCenter
    (h : Real)
    (f : ContinuumField ThreePointStencil) : Real :=
  centeredGraphLaplacianNumerator f / (h * h)

/-- Continuum second derivative of the quadratic model. -/
def quadraticContinuumSecondDerivative (a : Real) : Real :=
  2 * a

/--
Exact local consistency: the unscaled centered three-point graph-Laplacian
of a quadratic sample is `2 * a * h * h`.
-/
theorem centered_graph_laplacian_quadratic_numerator_exact
    (a b c h : Real) :
    centeredGraphLaplacianNumerator (sampledQuadraticField a b c h) =
      2 * a * h * h := by
  simp [centeredGraphLaplacianNumerator, sampledQuadraticField,
    threePointCoordinate]
  ring

/--
Exact scaled local consistency: for nonzero spacing, the centered graph
Laplacian of a quadratic sample matches the quadratic continuum second
derivative at the center.
-/
theorem centered_scaled_graph_laplacian_quadratic_exact
    (a b c h : Real)
    (h_nonzero : h * h ≠ 0) :
    centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticField a b c h) =
      quadraticContinuumSecondDerivative a := by
  have h_spacing : h ≠ 0 := by
    intro h_zero
    exact h_nonzero (by simp [h_zero])
  rw [centeredScaledGraphLaplacianAtCenter,
    centered_graph_laplacian_quadratic_numerator_exact,
    quadraticContinuumSecondDerivative]
  field_simp [h_spacing]

/--
The concrete theorem is local and quadratic only.  These are the exact
remaining obstructions before it could be promoted into the full A1A channel.
-/
inductive GraphLaplacianQuadraticConsistencyObstruction where
  | onlyQuadraticSamples
  | onlyOneInteriorStencil
  | noGeneralFunctionSpace
  | noRefinementFamilyLimit
  | noSampleReconstructionCompatibility
  | noUniformOrOperatorNormConvergence
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the concrete A1A obstruction list. -/
def graphLaplacianQuadraticConsistencyObstructionId :
    GraphLaplacianQuadraticConsistencyObstruction -> String
  | .onlyQuadraticSamples =>
      "A2A15A1A_OBSTRUCTION_ONLY_QUADRATIC_SAMPLES"
  | .onlyOneInteriorStencil =>
      "A2A15A1A_OBSTRUCTION_ONLY_ONE_INTERIOR_STENCIL"
  | .noGeneralFunctionSpace =>
      "A2A15A1A_OBSTRUCTION_NO_GENERAL_FUNCTION_SPACE"
  | .noRefinementFamilyLimit =>
      "A2A15A1A_OBSTRUCTION_NO_REFINEMENT_FAMILY_LIMIT"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noUniformOrOperatorNormConvergence =>
      "A2A15A1A_OBSTRUCTION_NO_UNIFORM_OR_OPERATOR_NORM_CONVERGENCE"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact concrete obstruction inventory for the theorem-facing A1A successor. -/
def graphLaplacianQuadraticConsistencyObstructionsV0 :
    List GraphLaplacianQuadraticConsistencyObstruction :=
  [ .onlyQuadraticSamples
  , .onlyOneInteriorStencil
  , .noGeneralFunctionSpace
  , .noRefinementFamilyLimit
  , .noSampleReconstructionCompatibility
  , .noUniformOrOperatorNormConvergence
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The concrete obstruction inventory is stable and explicit. -/
theorem graph_laplacian_quadratic_obstructions_v0_expected :
    graphLaplacianQuadraticConsistencyObstructionsV0 =
      [ .onlyQuadraticSamples
      , .onlyOneInteriorStencil
      , .noGeneralFunctionSpace
      , .noRefinementFamilyLimit
      , .noSampleReconstructionCompatibility
      , .noUniformOrOperatorNormConvergence
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording a concrete obstruction. -/
def graphLaplacianQuadraticSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, while the local proof remains explicit. -/
theorem graph_laplacian_quadratic_successor_kinds_v0_expected :
    graphLaplacianQuadraticSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the theorem-facing A1A quadratic consistency attempt. -/
structure GraphLaplacianQuadraticConsistencyStatus where
  quadratic_stencil_consistency_proved : Prop
  quadratic_stencil_consistency_proved_supplied :
    quadratic_stencil_consistency_proved
  concrete_obstruction_recorded : Prop
  concrete_obstruction_recorded_supplied : concrete_obstruction_recorded
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: a concrete quadratic-stencil consistency theorem is proved,
but the full A1A graph-Laplacian-to-continuum-Laplacian channel is retained.
-/
def graphLaplacianQuadraticConsistencyStatusV0 :
    GraphLaplacianQuadraticConsistencyStatus where
  quadratic_stencil_consistency_proved := True
  quadratic_stencil_consistency_proved_supplied := True.intro
  concrete_obstruction_recorded := True
  concrete_obstruction_recorded_supplied := True.intro
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1AQuadraticStencilConsistencyRetainedId
  outcome_id := graphLaplacianQuadraticConsistencyOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := graphLaplacianQuadraticSuccessorKindsV0
  obstruction_ids :=
    graphLaplacianQuadraticConsistencyObstructionsV0.map
      graphLaplacianQuadraticConsistencyObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def graphLaplacianQuadraticStatusV0 :
    GraphLaplacianQuadraticConsistencyStatus :=
  graphLaplacianQuadraticConsistencyStatusV0

/-- The theorem-facing successor proves its local quadratic consistency fact. -/
theorem graph_laplacian_quadratic_consistency_proved_v0 :
    graphLaplacianQuadraticStatusV0.quadratic_stencil_consistency_proved := by
  exact graphLaplacianQuadraticStatusV0.quadratic_stencil_consistency_proved_supplied

/-- The theorem-facing successor records the concrete obstruction list. -/
theorem graph_laplacian_quadratic_obstruction_recorded_v0 :
    graphLaplacianQuadraticStatusV0.concrete_obstruction_recorded := by
  exact graphLaplacianQuadraticStatusV0.concrete_obstruction_recorded_supplied

/-- The local quadratic consistency theorem does not close the full A1A channel. -/
theorem graph_laplacian_quadratic_full_a1a_not_closed_v0 :
    Not graphLaplacianQuadraticStatusV0.full_a1a_channel_closed := by
  exact graphLaplacianQuadraticStatusV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem graph_laplacian_quadratic_parent_retained_id_v0 :
    graphLaplacianQuadraticStatusV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The theorem-facing successor exposes its retained blocker id. -/
theorem graph_laplacian_quadratic_retained_id_v0 :
    graphLaplacianQuadraticStatusV0.retained_blocker_id =
      phase1Blocker003A2A15A1AQuadraticStencilConsistencyRetainedId := by
  rfl

/-- The theorem-facing successor exposes its outcome id. -/
theorem graph_laplacian_quadratic_outcome_id_v0 :
    graphLaplacianQuadraticStatusV0.outcome_id =
      graphLaplacianQuadraticConsistencyOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem graph_laplacian_quadratic_anti_loop_rule_id_v0 :
    graphLaplacianQuadraticStatusV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor is governed as obstruction-recording, with local proof explicit above. -/
theorem graph_laplacian_quadratic_successor_kinds_v0 :
    graphLaplacianQuadraticStatusV0.successor_kinds =
      graphLaplacianQuadraticSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem graph_laplacian_quadratic_phase2_not_authorized_v0 :
    Not graphLaplacianQuadraticStatusV0.phase2Authorized := by
  exact graphLaplacianQuadraticStatusV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianQuadraticConsistency
end QFT
end ToeFormal
