/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib.lean

Endpoint-package derivation attempt from mathlib Taylor data for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- define the coefficient/alignment data needed to derive the A1A8 endpoint
  package from mathlib endpoint Taylor machinery
- prove the right-endpoint remainder bound directly from mathlib for `0 <= h`
- prove that supplied scalar coefficient alignment plus the right mathlib
  bound and a supplied left-orientation bound constructs the A1A8 endpoint
  package
- feed that derived package through the already-proved symmetric Taylor and
  TaylorRemainderControl route
- retain the unsupplied scalar `taylorWithinEval` coefficient formula,
  centered two-sided package derivation, left endpoint orientation, uniform
  mesh convergence, full A1A closure, A2A15A1 closure, Phase 2 authorization,
  continuum closure, seam closure, empirical validation, and master-action
  promotion
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib

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
open ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment

set_option autoImplicit false

noncomputable section

/-- Retained blocker for deriving the endpoint package directly from mathlib. -/
def phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A9_ENDPOINT_PACKAGE_DERIVATION_" ++
    "FROM_MATHLIB_RETAINED"

/-- Outcome id for this endpoint-package derivation slice. -/
def graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId : String :=
  "RIGHT_ENDPOINT_TAYLOR_BOUND_DERIVED_ENDPOINT_PACKAGE_DERIVATION_" ++
    "RETAINED"

/-- Scalar order-three Taylor polynomial shape expected by the stencil route. -/
def scalarOrderThreeTaylorPolynomial
    (value first second third delta : Real) : Real :=
  value + first * delta + second * delta * delta / 2 +
    third * delta * delta * delta / 6

/--
Right endpoint remainder bound derived directly from the imported mathlib
Taylor theorem, with expansion centered at `x` and evaluated at `x + h`.
-/
theorem right_endpoint_remainder_bound_from_mathlib
    {f : Real -> Real}
    {x h C : Real}
    (h_nonnegative : 0 ≤ h)
    (hf : ContDiffOn Real (3 + 1) f (Set.Icc x (x + h)))
    (hC :
      ∀ y ∈ Set.Icc x (x + h),
        ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C) :
    |mathlibEndpointTaylorRemainder f x (x + h) (x + h)| ≤
      mathlibEndpointTaylorTolerance C x (x + h) := by
  have hx_upper : x ≤ x + h := by
    linarith
  have hendpoint : x + h ∈ Set.Icc x (x + h) := by
    exact ⟨hx_upper, le_rfl⟩
  exact
    mathlib_endpoint_taylor_remainder_bound
      (f := f) (base := x) (upper := x + h) (C := C)
      (endpoint := x + h) hx_upper hf hendpoint hC

/--
Data still needed to derive the A1A8 endpoint package from mathlib endpoint
Taylor machinery.  The right endpoint bound is theorem-derived below; the
scalar coefficient formula and left oriented endpoint package remain the
retained alignment obligations.
-/
structure EndpointPackageDerivationFromMathlibData
    (f : Real -> Real)
    (x h C : Real) where
  value : Real
  first_derivative : Real
  second_derivative : Real
  third_derivative : Real
  left_remainder : Real
  h_nonnegative : 0 ≤ h
  right_contDiffOn_center_to_endpoint :
    ContDiffOn Real (3 + 1) f (Set.Icc x (x + h))
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
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
  left_oriented_endpoint_bound_available : Prop
  left_oriented_endpoint_bound_available_supplied :
    left_oriented_endpoint_bound_available
  center_expansion : f x = value
  right_taylor_within_eval_eq_scalar_order_three :
    taylorWithinEval f 3 (Set.Icc x (x + h)) x (x + h) =
      scalarOrderThreeTaylorPolynomial
        value first_derivative second_derivative third_derivative h
  left_expansion :
    f (x - h) =
      scalarOrderThreeTaylorPolynomial
        value first_derivative second_derivative third_derivative (-h) +
        left_remainder
  left_remainder_bound_from_oriented_mathlib :
    |left_remainder| ≤
      mathlibEndpointTaylorTolerance C x (x - h)

/--
The right endpoint expansion equation follows from scalar coefficient
alignment for `taylorWithinEval` and the definition of the mathlib remainder.
-/
theorem right_endpoint_expansion_of_taylor_within_eval_alignment
    {f : Real -> Real}
    {x h value first second third : Real}
    (halign :
      taylorWithinEval f 3 (Set.Icc x (x + h)) x (x + h) =
        scalarOrderThreeTaylorPolynomial value first second third h) :
    f (x + h) =
      value + first * h + second * h * h / 2 +
        third * h * h * h / 6 +
        mathlibEndpointTaylorRemainder f x (x + h) (x + h) := by
  unfold mathlibEndpointTaylorRemainder
  rw [halign]
  unfold scalarOrderThreeTaylorPolynomial
  ring

/-- The supplied derivation data constructs the prior A1A8 endpoint package. -/
def mathlibEndpointPackageOfDerivationData
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C where
  value := data.value
  first_derivative := data.first_derivative
  second_derivative := data.second_derivative
  third_derivative := data.third_derivative
  left_remainder := data.left_remainder
  right_remainder :=
    mathlibEndpointTaylorRemainder f x (x + h) (x + h)
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  right_mathlib_endpoint_bound_available := True
  right_mathlib_endpoint_bound_available_supplied := True.intro
  left_mathlib_endpoint_bound_available :=
    data.left_oriented_endpoint_bound_available
  left_mathlib_endpoint_bound_available_supplied :=
    data.left_oriented_endpoint_bound_available_supplied
  right_centered_basepoint_alignment :=
    data.right_centered_basepoint_alignment
  right_centered_basepoint_alignment_supplied :=
    data.right_centered_basepoint_alignment_supplied
  left_centered_basepoint_alignment :=
    data.left_centered_basepoint_alignment
  left_centered_basepoint_alignment_supplied :=
    data.left_centered_basepoint_alignment_supplied
  right_taylor_within_eval_coefficient_alignment :=
    data.right_taylor_within_eval_coefficient_alignment
  right_taylor_within_eval_coefficient_alignment_supplied :=
    data.right_taylor_within_eval_coefficient_alignment_supplied
  left_taylor_within_eval_coefficient_alignment :=
    data.left_taylor_within_eval_coefficient_alignment
  left_taylor_within_eval_coefficient_alignment_supplied :=
    data.left_taylor_within_eval_coefficient_alignment_supplied
  center_expansion := data.center_expansion
  right_expansion :=
    right_endpoint_expansion_of_taylor_within_eval_alignment
      data.right_taylor_within_eval_eq_scalar_order_three
  left_expansion := by
    rw [data.left_expansion]
    unfold scalarOrderThreeTaylorPolynomial
    ring
  right_remainder_bound_from_mathlib :=
    right_endpoint_remainder_bound_from_mathlib
      data.h_nonnegative
      data.right_contDiffOn_center_to_endpoint
      data.right_fourth_derivative_bound
  left_remainder_bound_from_mathlib :=
    data.left_remainder_bound_from_oriented_mathlib

/-- The constructed package uses the theorem-derived right mathlib remainder. -/
theorem mathlib_endpoint_package_derivation_right_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    (mathlibEndpointPackageOfDerivationData data).right_remainder =
      mathlibEndpointTaylorRemainder f x (x + h) (x + h) := by
  rfl

/--
The supplied derivation data now feeds the prior symmetric Taylor bridge via
the A1A8 package constructor.
-/
def symmetricTaylorStencilBridgeOfEndpointPackageDerivation
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfDerivationData data)

/-- The supplied derivation data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfEndpointPackageDerivation
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfEndpointPackageDerivation data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfEndpointPackageDerivation data)

/-- Remaining obstructions after the endpoint-package derivation attempt. -/
inductive EndpointPackageDerivationFromMathlibObstruction where
  | noTaylorWithinEvalScalarCoefficientFormula
  | noLeftEndpointOrientationFromMathlib
  | noTwoSidedEndpointPackageFromSingleMathlibTheorem
  | noUniformMeshConvergence
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the endpoint package derivation obstruction list. -/
def endpointPackageDerivationFromMathlibObstructionId :
    EndpointPackageDerivationFromMathlibObstruction -> String
  | .noTaylorWithinEvalScalarCoefficientFormula =>
      "A2A15A1A9_OBSTRUCTION_NO_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
  | .noLeftEndpointOrientationFromMathlib =>
      "A2A15A1A9_OBSTRUCTION_NO_LEFT_ENDPOINT_ORIENTATION_FROM_MATHLIB"
  | .noTwoSidedEndpointPackageFromSingleMathlibTheorem =>
      "A2A15A1A9_OBSTRUCTION_NO_TWO_SIDED_ENDPOINT_PACKAGE_FROM_SINGLE_MATHLIB_THEOREM"
  | .noUniformMeshConvergence =>
      "A2A15A1A9_OBSTRUCTION_NO_UNIFORM_MESH_CONVERGENCE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A9_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A9_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A9_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A9_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the endpoint package derivation slice. -/
def endpointPackageDerivationFromMathlibObstructionsV0 :
    List EndpointPackageDerivationFromMathlibObstruction :=
  [ .noTaylorWithinEvalScalarCoefficientFormula
  , .noLeftEndpointOrientationFromMathlib
  , .noTwoSidedEndpointPackageFromSingleMathlibTheorem
  , .noUniformMeshConvergence
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The endpoint package derivation obstruction inventory is stable. -/
theorem endpoint_package_derivation_from_mathlib_obstructions_v0_expected :
    endpointPackageDerivationFromMathlibObstructionsV0 =
      [ .noTaylorWithinEvalScalarCoefficientFormula
      , .noLeftEndpointOrientationFromMathlib
      , .noTwoSidedEndpointPackageFromSingleMathlibTheorem
      , .noUniformMeshConvergence
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This theorem-facing slice records concrete obstruction. -/
def endpointPackageDerivationFromMathlibSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with partial proofs above. -/
theorem endpoint_package_derivation_from_mathlib_successor_kinds_v0_expected :
    endpointPackageDerivationFromMathlibSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the endpoint-package derivation slice. -/
structure EndpointPackageDerivationFromMathlibStatus where
  right_endpoint_bound_from_mathlib_proved : Prop
  right_endpoint_bound_from_mathlib_proved_supplied :
    right_endpoint_bound_from_mathlib_proved
  supplied_alignment_data_to_endpoint_package_proved : Prop
  supplied_alignment_data_to_endpoint_package_proved_supplied :
    supplied_alignment_data_to_endpoint_package_proved
  supplied_alignment_data_to_taylor_control_proved : Prop
  supplied_alignment_data_to_taylor_control_proved_supplied :
    supplied_alignment_data_to_taylor_control_proved
  endpoint_package_from_mathlib_fully_derived : Prop
  endpoint_package_from_mathlib_not_fully_derived :
    Not endpoint_package_from_mathlib_fully_derived
  taylor_within_eval_scalar_coefficients_proved : Prop
  taylor_within_eval_scalar_coefficients_not_proved :
    Not taylor_within_eval_scalar_coefficients_proved
  left_endpoint_orientation_proved : Prop
  left_endpoint_orientation_not_proved :
    Not left_endpoint_orientation_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_mathlib_alignment_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the right endpoint is theorem-derived from mathlib, but the
full two-sided endpoint package still depends on scalar coefficient alignment
and left endpoint orientation facts.
-/
def endpointPackageDerivationFromMathlibStatusV0 :
    EndpointPackageDerivationFromMathlibStatus where
  right_endpoint_bound_from_mathlib_proved := True
  right_endpoint_bound_from_mathlib_proved_supplied := True.intro
  supplied_alignment_data_to_endpoint_package_proved := True
  supplied_alignment_data_to_endpoint_package_proved_supplied := True.intro
  supplied_alignment_data_to_taylor_control_proved := True
  supplied_alignment_data_to_taylor_control_proved_supplied := True.intro
  endpoint_package_from_mathlib_fully_derived := False
  endpoint_package_from_mathlib_not_fully_derived := by
    intro h
    exact h
  taylor_within_eval_scalar_coefficients_proved := False
  taylor_within_eval_scalar_coefficients_not_proved := by
    intro h
    exact h
  left_endpoint_orientation_proved := False
  left_endpoint_orientation_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_mathlib_alignment_retained_blocker_id :=
    phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId
  outcome_id := graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointPackageDerivationFromMathlibSuccessorKindsV0
  obstruction_ids :=
    endpointPackageDerivationFromMathlibObstructionsV0.map
      endpointPackageDerivationFromMathlibObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def endpointPackageDerivationFromMathlibStatusReadoutV0 :
    EndpointPackageDerivationFromMathlibStatus :=
  endpointPackageDerivationFromMathlibStatusV0

/-- Short proof-facing status alias used to keep projection statements tidy. -/
def ePkgDerivStatusV0 :
    EndpointPackageDerivationFromMathlibStatus :=
  endpointPackageDerivationFromMathlibStatusReadoutV0

/-- The right endpoint Taylor bound is derived from mathlib. -/
theorem endpoint_package_derivation_right_endpoint_bound_proved_v0 :
    ePkgDerivStatusV0.right_endpoint_bound_from_mathlib_proved := by
  exact ePkgDerivStatusV0.right_endpoint_bound_from_mathlib_proved_supplied

/-- Supplied alignment data constructs the endpoint package. -/
theorem endpoint_package_derivation_to_endpoint_package_proved_v0 :
    ePkgDerivStatusV0.supplied_alignment_data_to_endpoint_package_proved := by
  exact
    ePkgDerivStatusV0.supplied_alignment_data_to_endpoint_package_proved_supplied

/-- Supplied alignment data feeds the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.supplied_alignment_data_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.supplied_alignment_data_to_taylor_control_proved_supplied

/-- The full endpoint package is not yet derived from mathlib alone. -/
theorem endpoint_package_derivation_from_mathlib_not_fully_derived_v0 :
    Not ePkgDerivStatusV0.endpoint_package_from_mathlib_fully_derived := by
  exact ePkgDerivStatusV0.endpoint_package_from_mathlib_not_fully_derived

/-- Scalar coefficient alignment for `taylorWithinEval` remains retained. -/
theorem endpoint_package_derivation_scalar_coefficients_not_proved_v0 :
    Not ePkgDerivStatusV0.taylor_within_eval_scalar_coefficients_proved := by
  exact ePkgDerivStatusV0.taylor_within_eval_scalar_coefficients_not_proved

/-- Left endpoint orientation remains retained. -/
theorem endpoint_package_derivation_left_orientation_not_proved_v0 :
    Not ePkgDerivStatusV0.left_endpoint_orientation_proved := by
  exact ePkgDerivStatusV0.left_endpoint_orientation_not_proved

/-- The endpoint package derivation slice does not close full A1A. -/
theorem endpoint_package_derivation_full_a1a_not_closed_v0 :
    Not ePkgDerivStatusV0.full_a1a_channel_closed := by
  exact ePkgDerivStatusV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem endpoint_package_derivation_parent_retained_id_v0 :
    ePkgDerivStatusV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A8 retained blocker remains exposed. -/
theorem endpoint_package_derivation_prior_a1a8_retained_id_v0 :
    ePkgDerivStatusV0.prior_mathlib_alignment_retained_blocker_id =
      phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem endpoint_package_derivation_retained_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem endpoint_package_derivation_outcome_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.outcome_id =
      graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem endpoint_package_derivation_anti_loop_rule_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem endpoint_package_derivation_successor_kinds_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.successor_kinds =
      endpointPackageDerivationFromMathlibSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A slice. -/
theorem endpoint_package_derivation_phase2_not_authorized_v0 :
    Not ePkgDerivStatusV0.phase2Authorized := by
  exact ePkgDerivStatusV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib
end QFT
end ToeFormal
