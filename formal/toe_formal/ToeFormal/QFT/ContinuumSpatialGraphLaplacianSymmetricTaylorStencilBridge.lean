/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge.lean

Symmetric two-sided Taylor-to-centered-stencil bridge for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- define the two Taylor expansions at `x + h` and `x - h`
- prove that odd Taylor terms cancel in the centered stencil numerator
- prove that the residual is the sum of the endpoint Taylor remainders
- prove that endpoint fourth-derivative remainder bounds imply the existing
  scale-normalized stencil remainder bound
- feed that bound into the existing `TaylorRemainderControl` route
- retain the proof that concrete smooth function/refinement data supplies the
  exact two-sided endpoint expansion package
- keep full A1A closure, A2A15A1 closure, Phase 2 authorization, continuum
  closure, seam closure, empirical validation, and master-action promotion out
  of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianConcreteTaylorRemainder

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianChannelCapstone
open ContinuumSpatialGraphLaplacianConcreteTaylorRemainder

set_option autoImplicit false

noncomputable section

/-- Retained blocker for supplying the concrete symmetric Taylor bridge data. -/
def phase1Blocker003A2A15A1A7SymmetricTaylorStencilBridgeRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A7_SYMMETRIC_TAYLOR_STENCIL_" ++
    "BRIDGE_RETAINED"

/-- Outcome id for the symmetric Taylor-to-stencil bridge. -/
def graphLaplacianSymmetricTaylorStencilBridgeOutcomeId : String :=
  "SYMMETRIC_TAYLOR_STENCIL_BRIDGE_ENDPOINT_REMAINDER_BOUND_RECORDED"

/-- Symmetric order-three Taylor polynomial sampled at `x-h`, `x`, and `x+h`. -/
def symmetricTaylorPolynomialStencil
    (value first second third h : Real) :
    ContinuumField ThreePointStencil
  | .left =>
      value - first * h + second * h * h / 2 - third * h * h * h / 6
  | .center => value
  | .right =>
      value + first * h + second * h * h / 2 + third * h * h * h / 6

/-- Endpoint Taylor remainders, with zero center remainder. -/
def symmetricEndpointTaylorRemainderField
    (leftRemainder rightRemainder : Real) :
    ContinuumField ThreePointStencil
  | .left => leftRemainder
  | .center => 0
  | .right => rightRemainder

/-- Point samples of a concrete function on a symmetric stencil. -/
def sampledFunctionOnSymmetricStencil
    (f : Real -> Real)
    (x h : Real) :
    ContinuumField ThreePointStencil
  | .left => f (x - h)
  | .center => f x
  | .right => f (x + h)

/-- Endpoint tolerance from the fourth-derivative Taylor remainder bound. -/
def symmetricTaylorEndpointRemainderTolerance
    (fourthDerivativeBound h : Real) : Real :=
  fourthDerivativeBound * (h * h) * (h * h) / 24

/-- Odd Taylor terms cancel in the centered stencil numerator. -/
theorem symmetric_taylor_polynomial_centered_numerator_exact
    (value first second third h : Real) :
    centeredGraphLaplacianNumerator
        (symmetricTaylorPolynomialStencil value first second third h) =
      second * h * h := by
  simp [centeredGraphLaplacianNumerator,
    symmetricTaylorPolynomialStencil]
  ring

/-- The centered numerator of the endpoint remainders is their sum. -/
theorem symmetric_endpoint_remainder_centered_numerator_exact
    (leftRemainder rightRemainder : Real) :
    centeredGraphLaplacianNumerator
        (symmetricEndpointTaylorRemainderField
          leftRemainder rightRemainder) =
      leftRemainder + rightRemainder := by
  simp [centeredGraphLaplacianNumerator,
    symmetricEndpointTaylorRemainderField]

/-- Endpoint absolute bounds imply the centered remainder numerator bound. -/
theorem symmetric_endpoint_remainder_centered_numerator_abs_bound
    (leftRemainder rightRemainder fourthDerivativeBound h : Real)
    (left_bound :
      |leftRemainder| ≤
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h)
    (right_bound :
      |rightRemainder| ≤
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h) :
    |centeredGraphLaplacianNumerator
        (symmetricEndpointTaylorRemainderField
          leftRemainder rightRemainder)| ≤
      fourthDerivativeStencilTolerance fourthDerivativeBound h *
        |h * h| := by
  have hsum :
      |leftRemainder + rightRemainder| ≤
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h +
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h := by
    exact (abs_add_le leftRemainder rightRemainder).trans
      (add_le_add left_bound right_bound)
  calc
    |centeredGraphLaplacianNumerator
        (symmetricEndpointTaylorRemainderField
          leftRemainder rightRemainder)| =
        |leftRemainder + rightRemainder| := by
          rw [symmetric_endpoint_remainder_centered_numerator_exact]
    _ ≤ symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h +
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h := hsum
    _ = fourthDerivativeStencilTolerance fourthDerivativeBound h *
        |h * h| := by
          have hsq_nonneg : 0 ≤ h * h := mul_self_nonneg h
          rw [abs_of_nonneg hsq_nonneg]
          unfold symmetricTaylorEndpointRemainderTolerance
            fourthDerivativeStencilTolerance
          ring

/--
Endpoint fourth-derivative bounds imply the exact scale-normalized stencil
remainder bound required by the A1A route.
-/
theorem symmetric_endpoint_remainders_supply_scaled_stencil_bound
    (leftRemainder rightRemainder fourthDerivativeBound h : Real)
    (h_nonzero : h * h ≠ 0)
    (left_bound :
      |leftRemainder| ≤
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h)
    (right_bound :
      |rightRemainder| ≤
        symmetricTaylorEndpointRemainderTolerance
          fourthDerivativeBound h) :
    scaledStencilRemainderErrorBound h
      (symmetricEndpointTaylorRemainderField
        leftRemainder rightRemainder)
      (fourthDerivativeStencilTolerance fourthDerivativeBound h) := by
  exact scaled_stencil_bound_of_centered_numerator_abs_bound
    h (fourthDerivativeStencilTolerance fourthDerivativeBound h)
    (symmetricEndpointTaylorRemainderField
      leftRemainder rightRemainder)
    h_nonzero
    (symmetric_endpoint_remainder_centered_numerator_abs_bound
      leftRemainder rightRemainder fourthDerivativeBound h
      left_bound right_bound)

/--
Two-sided Taylor expansion package for a concrete function on a symmetric
stencil.  Supplying this package is now the retained analytic bridge.
-/
structure SymmetricTaylorStencilBridge
    (f : Real -> Real)
    (x h fourthDerivativeBound : Real) where
  value : Real
  first_derivative : Real
  second_derivative : Real
  third_derivative : Real
  left_remainder : Real
  right_remainder : Real
  fourth_derivative_bound_nonnegative :
    0 ≤ fourthDerivativeBound
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied : two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  center_expansion : f x = value
  right_expansion :
    f (x + h) =
      value + first_derivative * h +
        second_derivative * h * h / 2 +
        third_derivative * h * h * h / 6 +
        right_remainder
  left_expansion :
    f (x - h) =
      value - first_derivative * h +
        second_derivative * h * h / 2 -
        third_derivative * h * h * h / 6 +
        left_remainder
  left_remainder_bound :
    |left_remainder| ≤
      symmetricTaylorEndpointRemainderTolerance
        fourthDerivativeBound h
  right_remainder_bound :
    |right_remainder| ≤
      symmetricTaylorEndpointRemainderTolerance
        fourthDerivativeBound h

/-- Remainder field associated to a supplied symmetric Taylor bridge. -/
def symmetricTaylorBridgeRemainderField
    {f : Real -> Real}
    {x h fourthDerivativeBound : Real}
    (bridge :
      SymmetricTaylorStencilBridge
        f x h fourthDerivativeBound) :
    ContinuumField ThreePointStencil :=
  symmetricEndpointTaylorRemainderField
    bridge.left_remainder bridge.right_remainder

/-- The supplied endpoint expansions decompose the sampled function stencil. -/
theorem sampled_function_symmetric_taylor_numerator_decomposition
    {f : Real -> Real}
    {x h fourthDerivativeBound : Real}
    (bridge :
      SymmetricTaylorStencilBridge
        f x h fourthDerivativeBound) :
    centeredGraphLaplacianNumerator
        (sampledFunctionOnSymmetricStencil f x h) =
      bridge.second_derivative * h * h +
        centeredGraphLaplacianNumerator
          (symmetricTaylorBridgeRemainderField bridge) := by
  simp [sampledFunctionOnSymmetricStencil,
    centeredGraphLaplacianNumerator,
    symmetricTaylorBridgeRemainderField,
    symmetricEndpointTaylorRemainderField,
    bridge.left_expansion,
    bridge.right_expansion,
    bridge.center_expansion]
  ring

/-- A supplied symmetric Taylor bridge feeds the scaled stencil bound. -/
theorem symmetric_taylor_bridge_supplies_scaled_stencil_bound
    {f : Real -> Real}
    {x h fourthDerivativeBound : Real}
    (h_nonzero : h * h ≠ 0)
    (bridge :
      SymmetricTaylorStencilBridge
        f x h fourthDerivativeBound) :
    scaledStencilRemainderErrorBound h
      (symmetricTaylorBridgeRemainderField bridge)
      (fourthDerivativeStencilTolerance fourthDerivativeBound h) := by
  exact symmetric_endpoint_remainders_supply_scaled_stencil_bound
    bridge.left_remainder bridge.right_remainder
    fourthDerivativeBound h h_nonzero
    bridge.left_remainder_bound
    bridge.right_remainder_bound

/-- A supplied symmetric Taylor bridge builds the prior TaylorRemainderControl. -/
def taylorRemainderControlOfSymmetricTaylorStencilBridge
    {f : Real -> Real}
    {x h fourthDerivativeBound : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (bridge :
      SymmetricTaylorStencilBridge
        f x h fourthDerivativeBound) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField bridge)
      (fourthDerivativeStencilTolerance fourthDerivativeBound h) where
  differentiability_order := 4
  differentiability_order_at_least_four := by norm_num
  bounded_fourth_derivative_or_equiv_smoothness :=
    bridge.c4_smoothness_on_symmetric_interval
  bounded_fourth_derivative_or_equiv_smoothness_supplied :=
    bridge.c4_smoothness_on_symmetric_interval_supplied
  fourth_derivative_bound := fourthDerivativeBound
  fourth_derivative_bound_nonnegative :=
    bridge.fourth_derivative_bound_nonnegative
  local_interval_model := bridge.two_sided_interval_model
  local_interval_model_supplied := bridge.two_sided_interval_model_supplied
  mesh_scale := |h|
  mesh_scale_matches_spacing := rfl
  refinement_parameter := refinementParameter
  refinement_parameter_positive := refinementParameterPositive
  refinement_scale_compatible :=
    bridge.sample_reconstruction_matches_stencil
  refinement_scale_compatible_supplied :=
    bridge.sample_reconstruction_matches_stencil_supplied
  scale_normalized_remainder_bound :=
    symmetric_taylor_bridge_supplies_scaled_stencil_bound
      h_nonzero bridge

/-- Remaining obstructions after proving the symmetric stencil algebra. -/
inductive SymmetricTaylorStencilBridgeObstruction where
  | noConcreteEndpointExpansionPackage
  | noMathlibTaylorEndpointAlignment
  | noUniformMeshConvergence
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the symmetric Taylor bridge obstruction list. -/
def symmetricTaylorStencilBridgeObstructionId :
    SymmetricTaylorStencilBridgeObstruction -> String
  | .noConcreteEndpointExpansionPackage =>
      "A2A15A1A7_OBSTRUCTION_NO_CONCRETE_ENDPOINT_EXPANSION_PACKAGE"
  | .noMathlibTaylorEndpointAlignment =>
      "A2A15A1A7_OBSTRUCTION_NO_MATHLIB_TAYLOR_ENDPOINT_ALIGNMENT"
  | .noUniformMeshConvergence =>
      "A2A15A1A7_OBSTRUCTION_NO_UNIFORM_MESH_CONVERGENCE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A7_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A7_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A7_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A7_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeObstructionsV0 :
    List SymmetricTaylorStencilBridgeObstruction :=
  [ .noConcreteEndpointExpansionPackage
  , .noMathlibTaylorEndpointAlignment
  , .noUniformMeshConvergence
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The symmetric Taylor obstruction inventory is stable and explicit. -/
theorem symmetric_taylor_stencil_bridge_obstructions_v0_expected :
    symmetricTaylorStencilBridgeObstructionsV0 =
      [ .noConcreteEndpointExpansionPackage
      , .noMathlibTaylorEndpointAlignment
      , .noUniformMeshConvergence
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This theorem-facing slice records concrete obstruction. -/
def symmetricTaylorStencilBridgeSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with bridge proofs above. -/
theorem symmetric_taylor_stencil_bridge_successor_kinds_v0_expected :
    symmetricTaylorStencilBridgeSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the symmetric Taylor-to-stencil bridge. -/
structure SymmetricTaylorStencilBridgeStatus where
  odd_terms_cancel_proved : Prop
  odd_terms_cancel_proved_supplied : odd_terms_cancel_proved
  remainder_sum_identity_proved : Prop
  remainder_sum_identity_proved_supplied :
    remainder_sum_identity_proved
  endpoint_bounds_to_scaled_bound_proved : Prop
  endpoint_bounds_to_scaled_bound_proved_supplied :
    endpoint_bounds_to_scaled_bound_proved
  bridge_to_taylor_control_proved : Prop
  bridge_to_taylor_control_proved_supplied :
    bridge_to_taylor_control_proved
  concrete_endpoint_expansion_package_proved : Prop
  concrete_endpoint_expansion_package_not_proved :
    Not concrete_endpoint_expansion_package_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_concrete_taylor_outcome_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the symmetric stencil algebra and bound propagation are proved,
but producing the endpoint expansion package from concrete smooth data remains
retained.
-/
def symmetricTaylorStencilBridgeStatusV0 :
    SymmetricTaylorStencilBridgeStatus where
  odd_terms_cancel_proved := True
  odd_terms_cancel_proved_supplied := True.intro
  remainder_sum_identity_proved := True
  remainder_sum_identity_proved_supplied := True.intro
  endpoint_bounds_to_scaled_bound_proved := True
  endpoint_bounds_to_scaled_bound_proved_supplied := True.intro
  bridge_to_taylor_control_proved := True
  bridge_to_taylor_control_proved_supplied := True.intro
  concrete_endpoint_expansion_package_proved := False
  concrete_endpoint_expansion_package_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_concrete_taylor_outcome_id :=
    graphLaplacianConcreteTaylorRemainderOutcomeId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A7SymmetricTaylorStencilBridgeRetainedId
  outcome_id := graphLaplacianSymmetricTaylorStencilBridgeOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := symmetricTaylorStencilBridgeSuccessorKindsV0
  obstruction_ids :=
    symmetricTaylorStencilBridgeObstructionsV0.map
      symmetricTaylorStencilBridgeObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def symmetricTaylorStencilBridgeStatusReadoutV0 :
    SymmetricTaylorStencilBridgeStatus :=
  symmetricTaylorStencilBridgeStatusV0

/-- Odd Taylor terms cancel in the centered stencil. -/
theorem symmetric_taylor_stencil_odd_terms_cancel_proved_v0 :
    SymmetricTaylorStencilBridgeStatus.odd_terms_cancel_proved
      symmetricTaylorStencilBridgeStatusReadoutV0 := by
  exact
    SymmetricTaylorStencilBridgeStatus.odd_terms_cancel_proved_supplied
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- The endpoint remainder sum identity is proved. -/
theorem symmetric_taylor_stencil_remainder_sum_identity_proved_v0 :
    SymmetricTaylorStencilBridgeStatus.remainder_sum_identity_proved
      symmetricTaylorStencilBridgeStatusReadoutV0 := by
  exact
    SymmetricTaylorStencilBridgeStatus.remainder_sum_identity_proved_supplied
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- Endpoint remainder bounds imply the scaled stencil bound. -/
theorem symmetric_taylor_stencil_endpoint_bounds_to_scaled_bound_proved_v0 :
    SymmetricTaylorStencilBridgeStatus.endpoint_bounds_to_scaled_bound_proved
      symmetricTaylorStencilBridgeStatusReadoutV0 := by
  exact
    SymmetricTaylorStencilBridgeStatus.endpoint_bounds_to_scaled_bound_proved_supplied
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- The supplied bridge feeds TaylorRemainderControl. -/
theorem symmetric_taylor_stencil_bridge_to_taylor_control_proved_v0 :
    SymmetricTaylorStencilBridgeStatus.bridge_to_taylor_control_proved
      symmetricTaylorStencilBridgeStatusReadoutV0 := by
  exact
    SymmetricTaylorStencilBridgeStatus.bridge_to_taylor_control_proved_supplied
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- Producing the endpoint expansion package remains retained. -/
theorem symmetric_taylor_stencil_endpoint_package_not_proved_v0 :
    Not
      (SymmetricTaylorStencilBridgeStatus.concrete_endpoint_expansion_package_proved
        symmetricTaylorStencilBridgeStatusReadoutV0) := by
  exact
    SymmetricTaylorStencilBridgeStatus.concrete_endpoint_expansion_package_not_proved
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- The symmetric Taylor bridge does not close full A1A. -/
theorem symmetric_taylor_stencil_full_a1a_not_closed_v0 :
    Not
      (SymmetricTaylorStencilBridgeStatus.full_a1a_channel_closed
        symmetricTaylorStencilBridgeStatusReadoutV0) := by
  exact
    SymmetricTaylorStencilBridgeStatus.full_a1a_channel_not_closed
      symmetricTaylorStencilBridgeStatusReadoutV0

/-- The parent A1A retained blocker remains exposed. -/
theorem symmetric_taylor_stencil_parent_retained_id_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior concrete Taylor outcome remains exposed. -/
theorem symmetric_taylor_stencil_prior_concrete_taylor_outcome_id_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.prior_concrete_taylor_outcome_id =
      graphLaplacianConcreteTaylorRemainderOutcomeId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem symmetric_taylor_stencil_retained_id_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A7SymmetricTaylorStencilBridgeRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem symmetric_taylor_stencil_outcome_id_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.outcome_id =
      graphLaplacianSymmetricTaylorStencilBridgeOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem symmetric_taylor_stencil_anti_loop_rule_id_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem symmetric_taylor_stencil_successor_kinds_v0 :
    symmetricTaylorStencilBridgeStatusReadoutV0.successor_kinds =
      symmetricTaylorStencilBridgeSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A slice. -/
theorem symmetric_taylor_stencil_phase2_not_authorized_v0 :
    Not symmetricTaylorStencilBridgeStatusReadoutV0.phase2Authorized := by
  exact symmetricTaylorStencilBridgeStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge
end QFT
end ToeFormal
