/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianTaylorRemainderControl.lean

Taylor/remainder-control surface for the A1A graph-Laplacian-to-continuum-
Laplacian channel.

Scope:
- state the regularity, local interval, mesh scale, and refinement data needed
  to turn the prior stencil remainder assumption into an analytic theorem
- connect a supplied Taylor-remainder-control object to the existing
  scale-normalized stencil remainder bound
- prove that supplied control feeds the local stencil error-bound theorem
- record that the actual Taylor/remainder-control theorem remains retained
- keep full graph-Laplacian-to-continuum-Laplacian convergence, continuum
  Laplacian construction, uniform refinement convergence, operator-domain
  closure, Phase 2 authorization, seam closure, empirical validation, and
  master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianStencilRemainder

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianTaylorRemainderControl

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder

set_option autoImplicit false

noncomputable section

/-- Retained blocker for deriving the A1A stencil remainder bound analytically. -/
def phase1Blocker003A2A15A1A2TaylorRemainderControlRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A2_TAYLOR_REMAINDER_CONTROL_RETAINED"

/-- Outcome id for the Taylor/remainder-control bridge surface. -/
def graphLaplacianTaylorRemainderControlOutcomeId : String :=
  "A2A15A1A2_TAYLOR_REMAINDER_CONTROL_SURFACE_RECORDED_RETAINED"

/--
Regularity and refinement data needed to justify the scale-normalized
remainder bound used by the stencil-remainder theorem.

The final field is still supplied evidence: this structure records the exact
analytic object the repo needs next, but does not derive it from real analysis.
-/
structure TaylorRemainderControl
    (h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (epsilon : Real) where
  differentiability_order : Nat
  differentiability_order_at_least_four : 4 ≤ differentiability_order
  bounded_fourth_derivative_or_equiv_smoothness : Prop
  bounded_fourth_derivative_or_equiv_smoothness_supplied :
    bounded_fourth_derivative_or_equiv_smoothness
  fourth_derivative_bound : Real
  fourth_derivative_bound_nonnegative : 0 ≤ fourth_derivative_bound
  local_interval_model : Prop
  local_interval_model_supplied : local_interval_model
  mesh_scale : Real
  mesh_scale_matches_spacing : mesh_scale = |h|
  refinement_parameter : Nat
  refinement_parameter_positive : 0 < refinement_parameter
  refinement_scale_compatible : Prop
  refinement_scale_compatible_supplied : refinement_scale_compatible
  scale_normalized_remainder_bound :
    scaledStencilRemainderErrorBound h remainder epsilon

/--
The Taylor/remainder-control object supplies the exact bound required by the
previous stencil-remainder theorem.
-/
theorem taylor_remainder_control_supplies_scaled_stencil_bound
    (h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (control : TaylorRemainderControl h remainder epsilon) :
    scaledStencilRemainderErrorBound h remainder epsilon := by
  exact control.scale_normalized_remainder_bound

/--
Conditional bridge: supplied Taylor/remainder control feeds the local
quadratic-plus-cubic-plus-remainder stencil error bound.
-/
theorem taylor_remainder_control_feeds_local_stencil_error_bound
    (a b c d h epsilon : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (control : TaylorRemainderControl h remainder epsilon) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField a b c d h remainder) -
      quadraticContinuumSecondDerivative a| ≤ epsilon := by
  exact centered_scaled_graph_laplacian_quadratic_cubic_remainder_error_bound
    a b c d h epsilon remainder h_nonzero
    control.scale_normalized_remainder_bound

/--
The bridge is explicit, but deriving the control object remains the retained
analytic theorem.
-/
inductive TaylorRemainderControlObstruction where
  | noTaylorRemainderTheorem
  | noBoundedFourthDerivativeConstruction
  | noLocalIntervalSemantics
  | noMeshRefinementLimit
  | noUniformRemainderControl
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the Taylor/remainder-control obstruction list. -/
def taylorRemainderControlObstructionId :
    TaylorRemainderControlObstruction -> String
  | .noTaylorRemainderTheorem =>
      "A2A15A1A2_OBSTRUCTION_NO_TAYLOR_REMAINDER_THEOREM"
  | .noBoundedFourthDerivativeConstruction =>
      "A2A15A1A2_OBSTRUCTION_NO_BOUNDED_FOURTH_DERIVATIVE_CONSTRUCTION"
  | .noLocalIntervalSemantics =>
      "A2A15A1A2_OBSTRUCTION_NO_LOCAL_INTERVAL_SEMANTICS"
  | .noMeshRefinementLimit =>
      "A2A15A1A2_OBSTRUCTION_NO_MESH_REFINEMENT_LIMIT"
  | .noUniformRemainderControl =>
      "A2A15A1A2_OBSTRUCTION_NO_UNIFORM_REMAINDER_CONTROL"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A2_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A2_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A2_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact obstruction inventory for the retained Taylor/remainder theorem. -/
def taylorRemainderControlObstructionsV0 :
    List TaylorRemainderControlObstruction :=
  [ .noTaylorRemainderTheorem
  , .noBoundedFourthDerivativeConstruction
  , .noLocalIntervalSemantics
  , .noMeshRefinementLimit
  , .noUniformRemainderControl
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The Taylor/remainder-control obstruction inventory is stable and explicit. -/
theorem taylor_remainder_control_obstructions_v0_expected :
    taylorRemainderControlObstructionsV0 =
      [ .noTaylorRemainderTheorem
      , .noBoundedFourthDerivativeConstruction
      , .noLocalIntervalSemantics
      , .noMeshRefinementLimit
      , .noUniformRemainderControl
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording concrete obstruction. -/
def taylorRemainderControlSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with bridge proof explicit. -/
theorem taylor_remainder_control_successor_kinds_v0_expected :
    taylorRemainderControlSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the theorem-facing Taylor/remainder-control surface. -/
structure TaylorRemainderControlStatus where
  control_object_defined : Prop
  control_object_defined_supplied : control_object_defined
  bridge_to_scaled_bound_proved : Prop
  bridge_to_scaled_bound_proved_supplied : bridge_to_scaled_bound_proved
  taylor_remainder_theorem_proved : Prop
  taylor_remainder_theorem_not_proved :
    Not taylor_remainder_theorem_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_stencil_remainder_outcome_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the required Taylor/remainder-control object and conditional
bridge are represented, but the actual Taylor theorem remains retained.
-/
def taylorRemainderControlStatusV0 :
    TaylorRemainderControlStatus where
  control_object_defined := True
  control_object_defined_supplied := True.intro
  bridge_to_scaled_bound_proved := True
  bridge_to_scaled_bound_proved_supplied := True.intro
  taylor_remainder_theorem_proved := False
  taylor_remainder_theorem_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_stencil_remainder_outcome_id :=
    graphLaplacianStencilRemainderOutcomeId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A2TaylorRemainderControlRetainedId
  outcome_id := graphLaplacianTaylorRemainderControlOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := taylorRemainderControlSuccessorKindsV0
  obstruction_ids :=
    taylorRemainderControlObstructionsV0.map
      taylorRemainderControlObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def taylorRemainderControlStatusReadoutV0 :
    TaylorRemainderControlStatus :=
  taylorRemainderControlStatusV0

/-- The Taylor/remainder-control object is now explicit. -/
theorem taylor_remainder_control_object_defined_v0 :
    taylorRemainderControlStatusReadoutV0.control_object_defined := by
  exact taylorRemainderControlStatusReadoutV0.control_object_defined_supplied

/-- The bridge from supplied control to the scaled stencil bound is proved. -/
theorem taylor_remainder_control_bridge_to_scaled_bound_proved_v0 :
    taylorRemainderControlStatusReadoutV0.bridge_to_scaled_bound_proved := by
  exact taylorRemainderControlStatusReadoutV0.bridge_to_scaled_bound_proved_supplied

/-- The actual Taylor/remainder theorem remains retained. -/
theorem taylor_remainder_control_theorem_not_proved_v0 :
    Not taylorRemainderControlStatusReadoutV0.taylor_remainder_theorem_proved := by
  exact taylorRemainderControlStatusReadoutV0.taylor_remainder_theorem_not_proved

/-- The Taylor/remainder-control surface does not close full A1A. -/
theorem taylor_remainder_control_full_a1a_not_closed_v0 :
    Not taylorRemainderControlStatusReadoutV0.full_a1a_channel_closed := by
  exact taylorRemainderControlStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem taylor_remainder_control_parent_retained_id_v0 :
    taylorRemainderControlStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The theorem-facing surface exposes the prior stencil-remainder outcome id. -/
theorem taylor_remainder_control_prior_stencil_outcome_id_v0 :
    taylorRemainderControlStatusReadoutV0.prior_stencil_remainder_outcome_id =
      graphLaplacianStencilRemainderOutcomeId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem taylor_remainder_control_retained_id_v0 :
    taylorRemainderControlStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A2TaylorRemainderControlRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem taylor_remainder_control_outcome_id_v0 :
    taylorRemainderControlStatusReadoutV0.outcome_id =
      graphLaplacianTaylorRemainderControlOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem taylor_remainder_control_anti_loop_rule_id_v0 :
    taylorRemainderControlStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem taylor_remainder_control_successor_kinds_v0 :
    taylorRemainderControlStatusReadoutV0.successor_kinds =
      taylorRemainderControlSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem taylor_remainder_control_phase2_not_authorized_v0 :
    Not taylorRemainderControlStatusReadoutV0.phase2Authorized := by
  exact taylorRemainderControlStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianTaylorRemainderControl
end QFT
end ToeFormal
