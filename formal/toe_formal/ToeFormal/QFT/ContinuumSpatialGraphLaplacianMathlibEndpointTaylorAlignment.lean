/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment.lean

Mathlib endpoint Taylor alignment surface for the A1A graph-Laplacian
channel.

Scope:
- define the exact endpoint Taylor expansion package needed by the A1A7
  symmetric Taylor-to-centered-stencil bridge
- expose the mathlib order-three Taylor endpoint remainder bound in the
  endpoint-package language
- prove the normalization bridge from mathlib's endpoint tolerance to the
  symmetric stencil endpoint tolerance, with the explicit constant conversion
  used by this route
- prove that a supplied endpoint alignment package constructs the prior A1A7
  symmetric Taylor bridge and TaylorRemainderControl route
- retain the proof that concrete smooth data supplies the endpoint expansion
  package and mathlib `taylorWithinEval` coefficient alignment
- keep uniform mesh convergence, full A1A closure, A2A15A1 closure, Phase 2
  authorization, continuum closure, seam closure, empirical validation, and
  master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment

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
open ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge

set_option autoImplicit false

noncomputable section

/-- Retained blocker for deriving the endpoint Taylor package from mathlib. -/
def phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A8_MATHLIB_ENDPOINT_TAYLOR_" ++
    "ALIGNMENT_RETAINED"

/-- Outcome id for this mathlib endpoint-alignment slice. -/
def graphLaplacianMathlibEndpointTaylorAlignmentOutcomeId : String :=
  "MATHLIB_ENDPOINT_TAYLOR_BOUND_MAPPED_ALIGNMENT_PACKAGE_RETAINED"

/--
The mathlib order-three endpoint remainder used by this slice: expansion at
`base`, evaluated at `endpoint`, with the interval upper endpoint kept
explicit.
-/
def mathlibEndpointTaylorRemainder
    (f : Real -> Real)
    (base upper endpoint : Real) : Real :=
  f endpoint -
    taylorWithinEval f 3 (Set.Icc base upper) base endpoint

/-- Mathlib's endpoint tolerance for the imported order-three bound. -/
def mathlibEndpointTaylorTolerance
    (C base endpoint : Real) : Real :=
  C * (endpoint - base) ^ (3 + 1) / (Nat.factorial 3 : Real)

/-- The imported mathlib endpoint Taylor theorem in endpoint-package form. -/
theorem mathlib_endpoint_taylor_remainder_bound
    {f : Real -> Real}
    {base upper C endpoint : Real}
    (hbase_upper : base ≤ upper)
    (hf : ContDiffOn Real (3 + 1) f (Set.Icc base upper))
    (hendpoint : endpoint ∈ Set.Icc base upper)
    (hC :
      ∀ y ∈ Set.Icc base upper,
        ‖iteratedDerivWithin (3 + 1) f (Set.Icc base upper) y‖ ≤ C) :
    |mathlibEndpointTaylorRemainder f base upper endpoint| ≤
      mathlibEndpointTaylorTolerance C base endpoint := by
  simpa [mathlibEndpointTaylorRemainder,
    mathlibEndpointTaylorTolerance, Real.norm_eq_abs]
    using
      concrete_taylor_order_three_remainder_bound
        (f := f) (a := base) (b := upper) (C := C)
        (x := endpoint) hbase_upper hf hendpoint hC

/--
Right endpoint normalization: mathlib's order-three bound is the symmetric
endpoint tolerance after explicitly using `4 * C` as the stencil fourth-bound.
-/
theorem mathlib_right_endpoint_tolerance_matches_symmetric_tolerance
    (C x h : Real) :
    mathlibEndpointTaylorTolerance C x (x + h) =
      symmetricTaylorEndpointRemainderTolerance (4 * C) h := by
  unfold mathlibEndpointTaylorTolerance
    symmetricTaylorEndpointRemainderTolerance
  norm_num [Nat.factorial]
  ring

/--
Left endpoint normalization: the fourth power removes the sign, again with
the explicit `4 * C` conversion into the stencil endpoint tolerance.
-/
theorem mathlib_left_endpoint_tolerance_matches_symmetric_tolerance
    (C x h : Real) :
    mathlibEndpointTaylorTolerance C x (x - h) =
      symmetricTaylorEndpointRemainderTolerance (4 * C) h := by
  unfold mathlibEndpointTaylorTolerance
    symmetricTaylorEndpointRemainderTolerance
  norm_num [Nat.factorial]
  ring

/--
Endpoint expansion package required to instantiate the prior A1A7 symmetric
Taylor bridge.  The actual derivation of these fields from mathlib's
`taylorWithinEval` coefficient semantics is the retained endpoint-alignment
obligation.
-/
structure MathlibEndpointTaylorExpansionPackage
    (f : Real -> Real)
    (x h C : Real) where
  value : Real
  first_derivative : Real
  second_derivative : Real
  third_derivative : Real
  left_remainder : Real
  right_remainder : Real
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  right_mathlib_endpoint_bound_available : Prop
  right_mathlib_endpoint_bound_available_supplied :
    right_mathlib_endpoint_bound_available
  left_mathlib_endpoint_bound_available : Prop
  left_mathlib_endpoint_bound_available_supplied :
    left_mathlib_endpoint_bound_available
  right_centered_basepoint_alignment : Prop
  right_centered_basepoint_alignment_supplied :
    right_centered_basepoint_alignment
  left_centered_basepoint_alignment : Prop
  left_centered_basepoint_alignment_supplied :
    left_centered_basepoint_alignment
  right_taylor_within_eval_coefficient_alignment : Prop
  right_taylor_within_eval_coefficient_alignment_supplied :
    right_taylor_within_eval_coefficient_alignment
  left_taylor_within_eval_coefficient_alignment : Prop
  left_taylor_within_eval_coefficient_alignment_supplied :
    left_taylor_within_eval_coefficient_alignment
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
  right_remainder_bound_from_mathlib :
    |right_remainder| ≤
      mathlibEndpointTaylorTolerance C x (x + h)
  left_remainder_bound_from_mathlib :
    |left_remainder| ≤
      mathlibEndpointTaylorTolerance C x (x - h)

/--
A supplied mathlib endpoint-alignment package constructs the A1A7 symmetric
Taylor bridge.  The factor `4 * C` records the normalization difference
between the imported mathlib bound and the endpoint tolerance used by the
stencil route.
-/
def symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    {f : Real -> Real}
    {x h C : Real}
    (pkg : MathlibEndpointTaylorExpansionPackage f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) where
  value := pkg.value
  first_derivative := pkg.first_derivative
  second_derivative := pkg.second_derivative
  third_derivative := pkg.third_derivative
  left_remainder := pkg.left_remainder
  right_remainder := pkg.right_remainder
  fourth_derivative_bound_nonnegative := by
    nlinarith [pkg.fourth_derivative_bound_nonnegative]
  c4_smoothness_on_symmetric_interval :=
    pkg.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    pkg.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := pkg.two_sided_interval_model
  two_sided_interval_model_supplied :=
    pkg.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    pkg.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    pkg.sample_reconstruction_matches_stencil_supplied
  center_expansion := pkg.center_expansion
  right_expansion := pkg.right_expansion
  left_expansion := pkg.left_expansion
  left_remainder_bound := by
    calc
      |pkg.left_remainder| ≤
          mathlibEndpointTaylorTolerance C x (x - h) :=
            pkg.left_remainder_bound_from_mathlib
      _ = symmetricTaylorEndpointRemainderTolerance (4 * C) h := by
            rw [mathlib_left_endpoint_tolerance_matches_symmetric_tolerance]
  right_remainder_bound := by
    calc
      |pkg.right_remainder| ≤
          mathlibEndpointTaylorTolerance C x (x + h) :=
            pkg.right_remainder_bound_from_mathlib
      _ = symmetricTaylorEndpointRemainderTolerance (4 * C) h := by
            rw [mathlib_right_endpoint_tolerance_matches_symmetric_tolerance]

/-- The resulting bridge has the expected remainder field. -/
theorem mathlib_endpoint_alignment_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (pkg : MathlibEndpointTaylorExpansionPackage f x h C) :
    symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfMathlibEndpointAlignment pkg) =
      symmetricEndpointTaylorRemainderField
        pkg.left_remainder pkg.right_remainder := by
  rfl

/--
A supplied mathlib endpoint-alignment package feeds the prior
TaylorRemainderControl route.
-/
def taylorRemainderControlOfMathlibEndpointAlignment
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (pkg : MathlibEndpointTaylorExpansionPackage f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfMathlibEndpointAlignment pkg))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfMathlibEndpointAlignment pkg)

/-- Remaining obstructions after the endpoint mathlib-bound mapping. -/
inductive MathlibEndpointTaylorAlignmentObstruction where
  | noCenteredTwoSidedBasepointAlignment
  | noTaylorWithinEvalCoefficientAlignment
  | noEndpointExpansionPackageFromSmoothData
  | noLeftEndpointOrientationDischarge
  | noUniformMeshConvergence
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the mathlib endpoint alignment obstruction list. -/
def mathlibEndpointTaylorAlignmentObstructionId :
    MathlibEndpointTaylorAlignmentObstruction -> String
  | .noCenteredTwoSidedBasepointAlignment =>
      "A2A15A1A8_OBSTRUCTION_NO_CENTERED_TWO_SIDED_BASEPOINT_ALIGNMENT"
  | .noTaylorWithinEvalCoefficientAlignment =>
      "A2A15A1A8_OBSTRUCTION_NO_TAYLOR_WITHIN_EVAL_COEFFICIENT_ALIGNMENT"
  | .noEndpointExpansionPackageFromSmoothData =>
      "A2A15A1A8_OBSTRUCTION_NO_ENDPOINT_EXPANSION_PACKAGE_FROM_SMOOTH_DATA"
  | .noLeftEndpointOrientationDischarge =>
      "A2A15A1A8_OBSTRUCTION_NO_LEFT_ENDPOINT_ORIENTATION_DISCHARGE"
  | .noUniformMeshConvergence =>
      "A2A15A1A8_OBSTRUCTION_NO_UNIFORM_MESH_CONVERGENCE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A8_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A8_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A8_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A8_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the endpoint alignment slice. -/
def mathlibEndpointTaylorAlignmentObstructionsV0 :
    List MathlibEndpointTaylorAlignmentObstruction :=
  [ .noCenteredTwoSidedBasepointAlignment
  , .noTaylorWithinEvalCoefficientAlignment
  , .noEndpointExpansionPackageFromSmoothData
  , .noLeftEndpointOrientationDischarge
  , .noUniformMeshConvergence
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The endpoint alignment obstruction inventory is stable and explicit. -/
theorem mathlib_endpoint_taylor_alignment_obstructions_v0_expected :
    mathlibEndpointTaylorAlignmentObstructionsV0 =
      [ .noCenteredTwoSidedBasepointAlignment
      , .noTaylorWithinEvalCoefficientAlignment
      , .noEndpointExpansionPackageFromSmoothData
      , .noLeftEndpointOrientationDischarge
      , .noUniformMeshConvergence
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This theorem-facing slice records concrete obstruction. -/
def mathlibEndpointTaylorAlignmentSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with mapping proofs above. -/
theorem mathlib_endpoint_taylor_alignment_successor_kinds_v0_expected :
    mathlibEndpointTaylorAlignmentSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the mathlib endpoint Taylor alignment slice. -/
structure MathlibEndpointTaylorAlignmentStatus where
  mathlib_endpoint_bound_exposed : Prop
  mathlib_endpoint_bound_exposed_supplied :
    mathlib_endpoint_bound_exposed
  tolerance_normalization_bridge_proved : Prop
  tolerance_normalization_bridge_proved_supplied :
    tolerance_normalization_bridge_proved
  supplied_package_to_symmetric_bridge_proved : Prop
  supplied_package_to_symmetric_bridge_proved_supplied :
    supplied_package_to_symmetric_bridge_proved
  supplied_package_to_taylor_control_proved : Prop
  supplied_package_to_taylor_control_proved_supplied :
    supplied_package_to_taylor_control_proved
  endpoint_alignment_from_mathlib_proved : Prop
  endpoint_alignment_from_mathlib_not_proved :
    Not endpoint_alignment_from_mathlib_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_symmetric_bridge_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: mathlib endpoint bounds and tolerance normalization are
mapped, but deriving the exact centered two-sided expansion package from
mathlib coefficient semantics remains retained.
-/
def mathlibEndpointTaylorAlignmentStatusV0 :
    MathlibEndpointTaylorAlignmentStatus where
  mathlib_endpoint_bound_exposed := True
  mathlib_endpoint_bound_exposed_supplied := True.intro
  tolerance_normalization_bridge_proved := True
  tolerance_normalization_bridge_proved_supplied := True.intro
  supplied_package_to_symmetric_bridge_proved := True
  supplied_package_to_symmetric_bridge_proved_supplied := True.intro
  supplied_package_to_taylor_control_proved := True
  supplied_package_to_taylor_control_proved_supplied := True.intro
  endpoint_alignment_from_mathlib_proved := False
  endpoint_alignment_from_mathlib_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_symmetric_bridge_retained_blocker_id :=
    phase1Blocker003A2A15A1A7SymmetricTaylorStencilBridgeRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId
  outcome_id := graphLaplacianMathlibEndpointTaylorAlignmentOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := mathlibEndpointTaylorAlignmentSuccessorKindsV0
  obstruction_ids :=
    mathlibEndpointTaylorAlignmentObstructionsV0.map
      mathlibEndpointTaylorAlignmentObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def mathlibEndpointTaylorAlignmentStatusReadoutV0 :
    MathlibEndpointTaylorAlignmentStatus :=
  mathlibEndpointTaylorAlignmentStatusV0

/-- The mathlib endpoint Taylor bound is exposed. -/
theorem mathlib_endpoint_taylor_bound_exposed_v0 :
    MathlibEndpointTaylorAlignmentStatus.mathlib_endpoint_bound_exposed
      mathlibEndpointTaylorAlignmentStatusReadoutV0 := by
  exact
    MathlibEndpointTaylorAlignmentStatus.mathlib_endpoint_bound_exposed_supplied
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- The endpoint tolerance normalization bridge is proved. -/
theorem mathlib_endpoint_taylor_tolerance_normalization_proved_v0 :
    MathlibEndpointTaylorAlignmentStatus.tolerance_normalization_bridge_proved
      mathlibEndpointTaylorAlignmentStatusReadoutV0 := by
  exact
    MathlibEndpointTaylorAlignmentStatus.tolerance_normalization_bridge_proved_supplied
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- A supplied endpoint package constructs the symmetric Taylor bridge. -/
theorem mathlib_endpoint_taylor_package_to_symmetric_bridge_proved_v0 :
    MathlibEndpointTaylorAlignmentStatus.supplied_package_to_symmetric_bridge_proved
      mathlibEndpointTaylorAlignmentStatusReadoutV0 := by
  exact
    MathlibEndpointTaylorAlignmentStatus.supplied_package_to_symmetric_bridge_proved_supplied
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- A supplied endpoint package feeds TaylorRemainderControl. -/
theorem mathlib_endpoint_taylor_package_to_taylor_control_proved_v0 :
    MathlibEndpointTaylorAlignmentStatus.supplied_package_to_taylor_control_proved
      mathlibEndpointTaylorAlignmentStatusReadoutV0 := by
  exact
    MathlibEndpointTaylorAlignmentStatus.supplied_package_to_taylor_control_proved_supplied
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- Deriving the endpoint alignment package from mathlib remains retained. -/
theorem mathlib_endpoint_taylor_alignment_from_mathlib_not_proved_v0 :
    Not
      (MathlibEndpointTaylorAlignmentStatus.endpoint_alignment_from_mathlib_proved
        mathlibEndpointTaylorAlignmentStatusReadoutV0) := by
  exact
    MathlibEndpointTaylorAlignmentStatus.endpoint_alignment_from_mathlib_not_proved
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- The mathlib endpoint alignment slice does not close full A1A. -/
theorem mathlib_endpoint_taylor_full_a1a_not_closed_v0 :
    Not
      (MathlibEndpointTaylorAlignmentStatus.full_a1a_channel_closed
        mathlibEndpointTaylorAlignmentStatusReadoutV0) := by
  exact
    MathlibEndpointTaylorAlignmentStatus.full_a1a_channel_not_closed
      mathlibEndpointTaylorAlignmentStatusReadoutV0

/-- The parent A1A retained blocker remains exposed. -/
theorem mathlib_endpoint_taylor_parent_retained_id_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior symmetric bridge retained blocker remains exposed. -/
theorem mathlib_endpoint_taylor_prior_symmetric_bridge_retained_id_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.prior_symmetric_bridge_retained_blocker_id =
      phase1Blocker003A2A15A1A7SymmetricTaylorStencilBridgeRetainedId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem mathlib_endpoint_taylor_retained_id_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem mathlib_endpoint_taylor_outcome_id_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.outcome_id =
      graphLaplacianMathlibEndpointTaylorAlignmentOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem mathlib_endpoint_taylor_anti_loop_rule_id_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem mathlib_endpoint_taylor_successor_kinds_v0 :
    mathlibEndpointTaylorAlignmentStatusReadoutV0.successor_kinds =
      mathlibEndpointTaylorAlignmentSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A slice. -/
theorem mathlib_endpoint_taylor_phase2_not_authorized_v0 :
    Not mathlibEndpointTaylorAlignmentStatusReadoutV0.phase2Authorized := by
  exact mathlibEndpointTaylorAlignmentStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment
end QFT
end ToeFormal
