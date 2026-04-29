/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianStencilRemainder.lean

Theorem-facing A1A successor after quadratic stencil consistency.

Scope:
- extend the local three-point graph-Laplacian calculation from quadratics to
  quadratic-plus-cubic-plus-remainder samples
- prove the symmetric stencil cancels the odd cubic contribution
- expose the exact scaled remainder error term and record a bounded-error
  condition as an explicit assumption, not as a derived analytic theorem
- keep full graph-Laplacian-to-continuum-Laplacian convergence, Taylor
  theorems, uniform remainder control, continuum operator semantics, Phase 2
  authorization, seam closure, empirical validation, and master-action
  promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianQuadraticConsistency

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianStencilRemainder

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the theorem-facing A1A stencil-remainder attempt. -/
def phase1Blocker003A2A15A1AStencilRemainderRetainedId : String :=
  "PHASE1-BLOCKER-003A2A15A1A_STENCIL_REMAINDER_ERROR_BOUND_" ++
    "RECORDED_FULL_CHANNEL_RETAINED"

/-- Outcome id for the A1A stencil-remainder successor. -/
def graphLaplacianStencilRemainderOutcomeId : String :=
  "A2A15A1A_STENCIL_REMAINDER_ERROR_BOUND_RECORDED"

/-- Quadratic plus odd cubic sample on the symmetric three-point stencil. -/
def sampledQuadraticCubicField (a b c d h : Real) :
    ContinuumField ThreePointStencil :=
  fun p =>
    let x := threePointCoordinate h p
    a * x * x + b * x + c + d * x * x * x

/--
Quadratic plus odd cubic plus an arbitrary remainder on the three-point
stencil.
-/
def sampledQuadraticCubicRemainderField
    (a b c d h : Real)
    (remainder : ContinuumField ThreePointStencil) :
    ContinuumField ThreePointStencil :=
  fun p => sampledQuadraticCubicField a b c d h p + remainder p

/--
The symmetric centered graph-Laplacian kills the odd cubic contribution and
keeps the same quadratic numerator.
-/
theorem centered_graph_laplacian_quadratic_cubic_numerator_exact
    (a b c d h : Real) :
    centeredGraphLaplacianNumerator
        (sampledQuadraticCubicField a b c d h) =
      2 * a * h * h := by
  simp [centeredGraphLaplacianNumerator, sampledQuadraticCubicField,
    threePointCoordinate]
  ring

/--
For an arbitrary remainder, the centered graph-Laplacian numerator is the
quadratic numerator plus the centered remainder numerator.
-/
theorem centered_graph_laplacian_quadratic_cubic_remainder_numerator_exact
    (a b c d h : Real)
    (remainder : ContinuumField ThreePointStencil) :
    centeredGraphLaplacianNumerator
        (sampledQuadraticCubicRemainderField a b c d h remainder) =
      2 * a * h * h + centeredGraphLaplacianNumerator remainder := by
  simp [centeredGraphLaplacianNumerator,
    sampledQuadraticCubicRemainderField, sampledQuadraticCubicField,
    threePointCoordinate]
  ring

/--
Exact scaled error identity: after subtracting the quadratic continuum second
derivative, the remaining error is precisely the scaled centered remainder
numerator.
-/
theorem centered_scaled_graph_laplacian_quadratic_cubic_remainder_error_exact
    (a b c d h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0) :
    centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField a b c d h remainder) -
      quadraticContinuumSecondDerivative a =
      centeredGraphLaplacianNumerator remainder / (h * h) := by
  have h_spacing : h ≠ 0 := by
    intro h_zero
    exact h_nonzero (by simp [h_zero])
  rw [centeredScaledGraphLaplacianAtCenter,
    centered_graph_laplacian_quadratic_cubic_remainder_numerator_exact,
    quadraticContinuumSecondDerivative]
  field_simp [h_spacing]
  ring

/--
Scale-normalized remainder bound.  This is an explicit retained analytic
condition, not a theorem derived from a Taylor expansion or a refinement
family.
-/
def scaledStencilRemainderErrorBound
    (h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (epsilon : Real) : Prop :=
  |centeredGraphLaplacianNumerator remainder / (h * h)| ≤ epsilon

/--
If the scale-normalized remainder bound is supplied, the local stencil error
is bounded by the supplied tolerance.
-/
theorem centered_scaled_graph_laplacian_quadratic_cubic_remainder_error_bound
    (a b c d h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (bound : scaledStencilRemainderErrorBound h remainder epsilon) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField a b c d h remainder) -
      quadraticContinuumSecondDerivative a| ≤ epsilon := by
  rw [centered_scaled_graph_laplacian_quadratic_cubic_remainder_error_exact
    a b c d h remainder h_nonzero]
  exact bound

/--
The local theorem records the exact error term, but the analytic bridge still
requires these missing ingredients before it can become full A1A convergence.
-/
inductive GraphLaplacianStencilRemainderObstruction where
  | onlyThreePointLocalStencil
  | remainderBoundAssumedNotDerived
  | noTaylorRemainderTheorem
  | noUniformRemainderControl
  | noRefinementFamilyLimit
  | noGeneralFunctionSpace
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the stencil-remainder obstruction list. -/
def graphLaplacianStencilRemainderObstructionId :
    GraphLaplacianStencilRemainderObstruction -> String
  | .onlyThreePointLocalStencil =>
      "A2A15A1A_OBSTRUCTION_ONLY_THREE_POINT_LOCAL_STENCIL"
  | .remainderBoundAssumedNotDerived =>
      "A2A15A1A_OBSTRUCTION_REMAINDER_BOUND_ASSUMED_NOT_DERIVED"
  | .noTaylorRemainderTheorem =>
      "A2A15A1A_OBSTRUCTION_NO_TAYLOR_REMAINDER_THEOREM"
  | .noUniformRemainderControl =>
      "A2A15A1A_OBSTRUCTION_NO_UNIFORM_REMAINDER_CONTROL"
  | .noRefinementFamilyLimit =>
      "A2A15A1A_OBSTRUCTION_NO_REFINEMENT_FAMILY_LIMIT"
  | .noGeneralFunctionSpace =>
      "A2A15A1A_OBSTRUCTION_NO_GENERAL_FUNCTION_SPACE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact concrete obstruction inventory for the stencil-remainder successor. -/
def graphLaplacianStencilRemainderObstructionsV0 :
    List GraphLaplacianStencilRemainderObstruction :=
  [ .onlyThreePointLocalStencil
  , .remainderBoundAssumedNotDerived
  , .noTaylorRemainderTheorem
  , .noUniformRemainderControl
  , .noRefinementFamilyLimit
  , .noGeneralFunctionSpace
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The stencil-remainder obstruction inventory is stable and explicit. -/
theorem graph_laplacian_stencil_remainder_obstructions_v0_expected :
    graphLaplacianStencilRemainderObstructionsV0 =
      [ .onlyThreePointLocalStencil
      , .remainderBoundAssumedNotDerived
      , .noTaylorRemainderTheorem
      , .noUniformRemainderControl
      , .noRefinementFamilyLimit
      , .noGeneralFunctionSpace
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording concrete obstruction. -/
def graphLaplacianStencilRemainderSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with local proof explicit above. -/
theorem graph_laplacian_stencil_remainder_successor_kinds_v0_expected :
    graphLaplacianStencilRemainderSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the theorem-facing A1A stencil-remainder attempt. -/
structure GraphLaplacianStencilRemainderStatus where
  cubic_cancellation_proved : Prop
  cubic_cancellation_proved_supplied : cubic_cancellation_proved
  exact_remainder_error_recorded : Prop
  exact_remainder_error_recorded_supplied : exact_remainder_error_recorded
  scaled_error_bound_recorded : Prop
  scaled_error_bound_recorded_supplied : scaled_error_bound_recorded
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_quadratic_outcome_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the cubic cancellation and exact remainder-error identity are
proved locally, but full A1A convergence remains retained.
-/
def graphLaplacianStencilRemainderStatusV0 :
    GraphLaplacianStencilRemainderStatus where
  cubic_cancellation_proved := True
  cubic_cancellation_proved_supplied := True.intro
  exact_remainder_error_recorded := True
  exact_remainder_error_recorded_supplied := True.intro
  scaled_error_bound_recorded := True
  scaled_error_bound_recorded_supplied := True.intro
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_quadratic_outcome_id := graphLaplacianQuadraticConsistencyOutcomeId
  retained_blocker_id := phase1Blocker003A2A15A1AStencilRemainderRetainedId
  outcome_id := graphLaplacianStencilRemainderOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := graphLaplacianStencilRemainderSuccessorKindsV0
  obstruction_ids :=
    graphLaplacianStencilRemainderObstructionsV0.map
      graphLaplacianStencilRemainderObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def graphLaplacianStencilRemainderStatusReadoutV0 :
    GraphLaplacianStencilRemainderStatus :=
  graphLaplacianStencilRemainderStatusV0

/-- The theorem-facing successor proves cubic cancellation. -/
theorem graph_laplacian_stencil_remainder_cubic_cancellation_proved_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.cubic_cancellation_proved := by
  exact graphLaplacianStencilRemainderStatusReadoutV0.cubic_cancellation_proved_supplied

/-- The theorem-facing successor records the exact remainder-error identity. -/
theorem graph_laplacian_stencil_remainder_exact_error_recorded_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.exact_remainder_error_recorded := by
  exact graphLaplacianStencilRemainderStatusReadoutV0.exact_remainder_error_recorded_supplied

/-- The theorem-facing successor records a scaled error-bound condition. -/
theorem graph_laplacian_stencil_remainder_bound_recorded_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.scaled_error_bound_recorded := by
  exact graphLaplacianStencilRemainderStatusReadoutV0.scaled_error_bound_recorded_supplied

/-- The local stencil-remainder theorem does not close the full A1A channel. -/
theorem graph_laplacian_stencil_remainder_full_a1a_not_closed_v0 :
    Not graphLaplacianStencilRemainderStatusReadoutV0.full_a1a_channel_closed := by
  exact graphLaplacianStencilRemainderStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem graph_laplacian_stencil_remainder_parent_retained_id_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The theorem-facing successor exposes the prior quadratic outcome id. -/
theorem graph_laplacian_stencil_remainder_prior_quadratic_outcome_id_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.prior_quadratic_outcome_id =
      graphLaplacianQuadraticConsistencyOutcomeId := by
  rfl

/-- The theorem-facing successor exposes its retained blocker id. -/
theorem graph_laplacian_stencil_remainder_retained_id_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1AStencilRemainderRetainedId := by
  rfl

/-- The theorem-facing successor exposes its outcome id. -/
theorem graph_laplacian_stencil_remainder_outcome_id_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.outcome_id =
      graphLaplacianStencilRemainderOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem graph_laplacian_stencil_remainder_anti_loop_rule_id_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem graph_laplacian_stencil_remainder_successor_kinds_v0 :
    graphLaplacianStencilRemainderStatusReadoutV0.successor_kinds =
      graphLaplacianStencilRemainderSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem graph_laplacian_stencil_remainder_phase2_not_authorized_v0 :
    Not graphLaplacianStencilRemainderStatusReadoutV0.phase2Authorized := by
  exact graphLaplacianStencilRemainderStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianStencilRemainder
end QFT
end ToeFormal
