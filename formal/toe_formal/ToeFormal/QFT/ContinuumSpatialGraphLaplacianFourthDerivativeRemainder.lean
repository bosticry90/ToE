/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianFourthDerivativeRemainder.lean

Fourth-derivative-bound to stencil-remainder bridge for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- state the concrete fourth-derivative-bound certificate needed to derive the
  scale-normalized stencil remainder bound
- record the local Taylor formula, fourth-order remainder formula, centered
  residual estimate, and refinement/uniformity condition as supplied analytic
  facts
- prove that such a certificate constructs the prior TaylorRemainderControl
  object and conditionally feeds the local stencil error-bound theorem
- retain the actual real-analysis theorem deriving that certificate
- keep full graph-Laplacian-to-continuum-Laplacian convergence, continuum
  Laplacian construction, sample/reconstruction compatibility, operator-domain
  closure, Phase 2 authorization, seam closure, empirical validation, and
  master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianTaylorRemainderControl

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianFourthDerivativeRemainder

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl

set_option autoImplicit false

noncomputable section

/-- Retained blocker for deriving stencil remainder control from fourth derivatives. -/
def phase1Blocker003A2A15A1A3FourthDerivativeRemainderRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A3_FOURTH_DERIVATIVE_BOUND_TO_" ++
    "STENCIL_REMAINDER_RETAINED"

/-- Outcome id for the fourth-derivative-bound bridge surface. -/
def graphLaplacianFourthDerivativeRemainderOutcomeId : String :=
  "A2A15A1A3_FOURTH_DERIVATIVE_BOUND_TO_STENCIL_REMAINDER_" ++
    "SURFACE_RECORDED_RETAINED"

/-- The tolerance scale produced by a fourth-derivative bound at spacing `h`. -/
def fourthDerivativeStencilTolerance (fourthDerivativeBound h : Real) :
    Real :=
  fourthDerivativeBound * (h * h) / 12

/--
Certificate shape required to derive the stencil remainder bound from a
bounded fourth derivative.

The final scale-normalized bound is still supplied evidence.  This records
the exact real-analysis theorem that must later be proved rather than hiding
it inside the stencil algebra.
-/
structure FourthDerivativeBoundToStencilRemainder
    (h : Real)
    (remainder : ContinuumField ThreePointStencil) where
  differentiability_order : Nat
  differentiability_order_at_least_four : 4 ≤ differentiability_order
  fourth_derivative_bound : Real
  fourth_derivative_bound_nonnegative : 0 ≤ fourth_derivative_bound
  bounded_fourth_derivative_on_interval : Prop
  bounded_fourth_derivative_on_interval_supplied :
    bounded_fourth_derivative_on_interval
  local_interval_model : Prop
  local_interval_model_supplied : local_interval_model
  local_taylor_formula : Prop
  local_taylor_formula_supplied : local_taylor_formula
  fourth_order_remainder_formula : Prop
  fourth_order_remainder_formula_supplied : fourth_order_remainder_formula
  centered_stencil_residual_estimate : Prop
  centered_stencil_residual_estimate_supplied :
    centered_stencil_residual_estimate
  mesh_scale : Real
  mesh_scale_matches_spacing : mesh_scale = |h|
  refinement_parameter : Nat
  refinement_parameter_positive : 0 < refinement_parameter
  refinement_uniformity_condition : Prop
  refinement_uniformity_condition_supplied : refinement_uniformity_condition
  scale_normalized_bound_from_fourth_derivative :
    scaledStencilRemainderErrorBound h remainder
      (fourthDerivativeStencilTolerance fourth_derivative_bound h)

/--
The fourth-derivative certificate supplies the scale-normalized stencil bound
with the tolerance determined by its fourth-derivative bound and spacing.
-/
theorem fourth_derivative_bound_supplies_scaled_stencil_bound
    (h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (cert : FourthDerivativeBoundToStencilRemainder h remainder) :
    scaledStencilRemainderErrorBound h remainder
      (fourthDerivativeStencilTolerance
        cert.fourth_derivative_bound h) := by
  exact cert.scale_normalized_bound_from_fourth_derivative

/-- A fourth-derivative certificate builds the prior TaylorRemainderControl. -/
def fourthDerivativeBoundToTaylorRemainderControl
    (h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (cert : FourthDerivativeBoundToStencilRemainder h remainder) :
    TaylorRemainderControl h remainder
      (fourthDerivativeStencilTolerance
        cert.fourth_derivative_bound h) where
  differentiability_order := cert.differentiability_order
  differentiability_order_at_least_four :=
    cert.differentiability_order_at_least_four
  bounded_fourth_derivative_or_equiv_smoothness :=
    cert.bounded_fourth_derivative_on_interval
  bounded_fourth_derivative_or_equiv_smoothness_supplied :=
    cert.bounded_fourth_derivative_on_interval_supplied
  fourth_derivative_bound := cert.fourth_derivative_bound
  fourth_derivative_bound_nonnegative :=
    cert.fourth_derivative_bound_nonnegative
  local_interval_model := cert.local_interval_model
  local_interval_model_supplied := cert.local_interval_model_supplied
  mesh_scale := cert.mesh_scale
  mesh_scale_matches_spacing := cert.mesh_scale_matches_spacing
  refinement_parameter := cert.refinement_parameter
  refinement_parameter_positive := cert.refinement_parameter_positive
  refinement_scale_compatible := cert.refinement_uniformity_condition
  refinement_scale_compatible_supplied :=
    cert.refinement_uniformity_condition_supplied
  scale_normalized_remainder_bound :=
    cert.scale_normalized_bound_from_fourth_derivative

/--
Conditional bridge: a fourth-derivative certificate feeds the local
quadratic-plus-cubic-plus-remainder stencil error-bound theorem.
-/
theorem fourth_derivative_bound_feeds_local_stencil_error_bound
    (a b c d h : Real)
    (remainder : ContinuumField ThreePointStencil)
    (h_nonzero : h * h ≠ 0)
    (cert : FourthDerivativeBoundToStencilRemainder h remainder) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField a b c d h remainder) -
      quadraticContinuumSecondDerivative a| ≤
      fourthDerivativeStencilTolerance
        cert.fourth_derivative_bound h := by
  exact taylor_remainder_control_feeds_local_stencil_error_bound
    a b c d h
    (fourthDerivativeStencilTolerance cert.fourth_derivative_bound h)
    remainder h_nonzero
    (fourthDerivativeBoundToTaylorRemainderControl h remainder cert)

/--
The bridge is explicit, but proving the certificate from concrete smoothness
and local Taylor theory remains the retained analytic theorem.
-/
inductive FourthDerivativeRemainderObstruction where
  | noConcreteFourthDerivativeOperator
  | noBoundedFourthDerivativeTheorem
  | noLocalTaylorFormula
  | noFourthOrderRemainderFormula
  | noCenteredResidualEstimate
  | noUniformRefinementControl
  | noFunctionSpaceSemantics
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the fourth-derivative remainder obstruction list. -/
def fourthDerivativeRemainderObstructionId :
    FourthDerivativeRemainderObstruction -> String
  | .noConcreteFourthDerivativeOperator =>
      "A2A15A1A3_OBSTRUCTION_NO_CONCRETE_FOURTH_DERIVATIVE_OPERATOR"
  | .noBoundedFourthDerivativeTheorem =>
      "A2A15A1A3_OBSTRUCTION_NO_BOUNDED_FOURTH_DERIVATIVE_THEOREM"
  | .noLocalTaylorFormula =>
      "A2A15A1A3_OBSTRUCTION_NO_LOCAL_TAYLOR_FORMULA"
  | .noFourthOrderRemainderFormula =>
      "A2A15A1A3_OBSTRUCTION_NO_FOURTH_ORDER_REMAINDER_FORMULA"
  | .noCenteredResidualEstimate =>
      "A2A15A1A3_OBSTRUCTION_NO_CENTERED_RESIDUAL_ESTIMATE"
  | .noUniformRefinementControl =>
      "A2A15A1A3_OBSTRUCTION_NO_UNIFORM_REFINEMENT_CONTROL"
  | .noFunctionSpaceSemantics =>
      "A2A15A1A3_OBSTRUCTION_NO_FUNCTION_SPACE_SEMANTICS"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A3_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A3_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A3_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact obstruction inventory for the retained fourth-derivative theorem. -/
def fourthDerivativeRemainderObstructionsV0 :
    List FourthDerivativeRemainderObstruction :=
  [ .noConcreteFourthDerivativeOperator
  , .noBoundedFourthDerivativeTheorem
  , .noLocalTaylorFormula
  , .noFourthOrderRemainderFormula
  , .noCenteredResidualEstimate
  , .noUniformRefinementControl
  , .noFunctionSpaceSemantics
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The fourth-derivative obstruction inventory is stable and explicit. -/
theorem fourth_derivative_remainder_obstructions_v0_expected :
    fourthDerivativeRemainderObstructionsV0 =
      [ .noConcreteFourthDerivativeOperator
      , .noBoundedFourthDerivativeTheorem
      , .noLocalTaylorFormula
      , .noFourthOrderRemainderFormula
      , .noCenteredResidualEstimate
      , .noUniformRefinementControl
      , .noFunctionSpaceSemantics
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording concrete obstruction. -/
def fourthDerivativeRemainderSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with bridge proof explicit. -/
theorem fourth_derivative_remainder_successor_kinds_v0_expected :
    fourthDerivativeRemainderSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the fourth-derivative-bound bridge surface. -/
structure FourthDerivativeRemainderStatus where
  certificate_shape_defined : Prop
  certificate_shape_defined_supplied : certificate_shape_defined
  bridge_to_taylor_control_proved : Prop
  bridge_to_taylor_control_proved_supplied :
    bridge_to_taylor_control_proved
  local_error_bound_conditionally_proved : Prop
  local_error_bound_conditionally_proved_supplied :
    local_error_bound_conditionally_proved
  fourth_derivative_bound_theorem_proved : Prop
  fourth_derivative_bound_theorem_not_proved :
    Not fourth_derivative_bound_theorem_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_taylor_control_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the fourth-derivative certificate shape and conditional bridge
are represented, but deriving the certificate remains retained.
-/
def fourthDerivativeRemainderStatusV0 :
    FourthDerivativeRemainderStatus where
  certificate_shape_defined := True
  certificate_shape_defined_supplied := True.intro
  bridge_to_taylor_control_proved := True
  bridge_to_taylor_control_proved_supplied := True.intro
  local_error_bound_conditionally_proved := True
  local_error_bound_conditionally_proved_supplied := True.intro
  fourth_derivative_bound_theorem_proved := False
  fourth_derivative_bound_theorem_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_taylor_control_retained_blocker_id :=
    phase1Blocker003A2A15A1A2TaylorRemainderControlRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A3FourthDerivativeRemainderRetainedId
  outcome_id := graphLaplacianFourthDerivativeRemainderOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := fourthDerivativeRemainderSuccessorKindsV0
  obstruction_ids :=
    fourthDerivativeRemainderObstructionsV0.map
      fourthDerivativeRemainderObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def fourthDerivativeRemainderStatusReadoutV0 :
    FourthDerivativeRemainderStatus :=
  fourthDerivativeRemainderStatusV0

/-- The fourth-derivative certificate shape is now explicit. -/
theorem fourth_derivative_remainder_certificate_shape_defined_v0 :
    fourthDerivativeRemainderStatusReadoutV0.certificate_shape_defined := by
  exact fourthDerivativeRemainderStatusReadoutV0.certificate_shape_defined_supplied

/-- The bridge to TaylorRemainderControl is recorded as proved. -/
theorem fourth_derivative_remainder_bridge_to_taylor_control_proved_v0 :
    fourthDerivativeRemainderStatusReadoutV0.bridge_to_taylor_control_proved := by
  exact fourthDerivativeRemainderStatusReadoutV0.bridge_to_taylor_control_proved_supplied

/-- The conditional local error-bound bridge is recorded as proved. -/
theorem fourth_derivative_remainder_local_error_bound_proved_v0 :
    fourthDerivativeRemainderStatusReadoutV0.local_error_bound_conditionally_proved := by
  exact
    FourthDerivativeRemainderStatus.local_error_bound_conditionally_proved_supplied
      fourthDerivativeRemainderStatusReadoutV0

/-- The actual fourth-derivative-bound theorem remains retained. -/
theorem fourth_derivative_remainder_theorem_not_proved_v0 :
    Not fourthDerivativeRemainderStatusReadoutV0.fourth_derivative_bound_theorem_proved := by
  exact
    FourthDerivativeRemainderStatus.fourth_derivative_bound_theorem_not_proved
      fourthDerivativeRemainderStatusReadoutV0

/-- The fourth-derivative bridge does not close full A1A. -/
theorem fourth_derivative_remainder_full_a1a_not_closed_v0 :
    Not fourthDerivativeRemainderStatusReadoutV0.full_a1a_channel_closed := by
  exact fourthDerivativeRemainderStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem fourth_derivative_remainder_parent_retained_id_v0 :
    fourthDerivativeRemainderStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A2 Taylor-control retained blocker remains exposed. -/
theorem fourth_derivative_remainder_prior_taylor_retained_id_v0 :
    fourthDerivativeRemainderStatusReadoutV0.prior_taylor_control_retained_blocker_id =
      phase1Blocker003A2A15A1A2TaylorRemainderControlRetainedId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem fourth_derivative_remainder_retained_id_v0 :
    fourthDerivativeRemainderStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A3FourthDerivativeRemainderRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem fourth_derivative_remainder_outcome_id_v0 :
    fourthDerivativeRemainderStatusReadoutV0.outcome_id =
      graphLaplacianFourthDerivativeRemainderOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem fourth_derivative_remainder_anti_loop_rule_id_v0 :
    fourthDerivativeRemainderStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem fourth_derivative_remainder_successor_kinds_v0 :
    fourthDerivativeRemainderStatusReadoutV0.successor_kinds =
      fourthDerivativeRemainderSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem fourth_derivative_remainder_phase2_not_authorized_v0 :
    Not fourthDerivativeRemainderStatusReadoutV0.phase2Authorized := by
  exact fourthDerivativeRemainderStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
end QFT
end ToeFormal
