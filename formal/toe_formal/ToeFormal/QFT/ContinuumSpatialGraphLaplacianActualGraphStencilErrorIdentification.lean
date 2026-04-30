/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianActualGraphStencilErrorIdentification.lean

Actual graph-stencil error identification for the A1A graph-Laplacian route.

Scope:
- define the actual graph-channel local stencil-error value as the centered
  graph-Laplacian action on the sampled function stencil
- prove that this actual local error equals the endpoint-package
  stencil-error value already bounded in A1A15
- lift the equality to the refinement-indexed error sequence
- transfer the A1A15 order-h^2 bound, convergence theorem, A1A12 mode, and
  A1A11 evidence object to the actual graph-action error sequence
- retain the final parent graph-channel semantic closure review
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianActualGraphStencilErrorIdentification

open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge
open ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment
open ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
open ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
open ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound
open ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound

set_option autoImplicit false

noncomputable section

/--
Retained blocker after identifying the actual graph-action stencil error:
review and close the remaining parent graph-channel semantic fields.
-/
def phase1Blocker003A2A15A1A16GraphChannelSemanticClosureRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A16_GRAPH_CHANNEL_SEMANTIC_" ++
    "CLOSURE_RETAINED"

/-- Outcome id for the A1A16 actual graph-stencil identification. -/
def graphLaplacianActualGraphStencilErrorIdentificationOutcomeId : String :=
  "ACTUAL_GRAPH_STENCIL_ERROR_IDENTIFIED_WITH_ENDPOINT_PACKAGE_" ++
    "ERROR_A1A_CHANNEL_READY_FOR_CLOSURE_REVIEW"

/--
The actual graph-channel local stencil error: the centered graph-Laplacian
action applied to the sampled function values, minus the continuum second
derivative coefficient selected by the two-sided endpoint package.
-/
def actualGraphChannelStencilErrorOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    Real :=
  centeredScaledGraphLaplacianAtCenter h
      (sampledFunctionOnSymmetricStencil f x h) -
    quadraticContinuumSecondDerivative
      ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)

/--
The sampled function stencil is exactly the quadratic/cubic/remainder field
reconstructed by the endpoint package.
-/
theorem sampled_function_equals_endpoint_package_reconstructed_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    sampledFunctionOnSymmetricStencil f x h =
      sampledQuadraticCubicRemainderField
        ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)
        (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).first_derivative
        (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).value
        ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).third_derivative / 6)
        h
        (symmetricTaylorBridgeRemainderField
          (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data)) := by
  funext p
  cases p
  · simp [sampledFunctionOnSymmetricStencil,
      sampledQuadraticCubicRemainderField, sampledQuadraticCubicField,
      symmetricTaylorBridgeRemainderField,
      symmetricEndpointTaylorRemainderField,
      symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage,
      symmetricTaylorStencilBridgeOfMathlibEndpointAlignment,
      threePointCoordinate,
      (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data).left_expansion]
    ring_nf
  · simp [sampledFunctionOnSymmetricStencil,
      sampledQuadraticCubicRemainderField, sampledQuadraticCubicField,
      symmetricTaylorBridgeRemainderField,
      symmetricEndpointTaylorRemainderField,
      symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage,
      symmetricTaylorStencilBridgeOfMathlibEndpointAlignment,
      threePointCoordinate,
      (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data).center_expansion]
  · simp [sampledFunctionOnSymmetricStencil,
      sampledQuadraticCubicRemainderField, sampledQuadraticCubicField,
      symmetricTaylorBridgeRemainderField,
      symmetricEndpointTaylorRemainderField,
      symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage,
      symmetricTaylorStencilBridgeOfMathlibEndpointAlignment,
      threePointCoordinate,
      (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data).right_expansion]
    ring_nf

/--
The actual graph-action local error equals the endpoint-package stencil-error
value already bounded in A1A15.
-/
theorem actual_graph_stencil_error_equals_endpoint_package_error_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    actualGraphChannelStencilErrorOfGlobalCenteredAlignmentData data =
      endpointPackageStencilErrorOfGlobalCenteredAlignmentData data := by
  rw [actualGraphChannelStencilErrorOfGlobalCenteredAlignmentData,
    endpointPackageStencilErrorOfGlobalCenteredAlignmentData,
    sampled_function_equals_endpoint_package_reconstructed_field_v0 data]

/-- The actual graph-action stencil-error sequence over the concrete mesh. -/
def actualGraphChannelStencilErrorSequence
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    Nat -> Real :=
  fun n =>
    actualGraphChannelStencilErrorOfGlobalCenteredAlignmentData
      (family.endpoint_data n)

/-- The actual graph-action error sequence equals the endpoint-package sequence. -/
theorem actual_graph_stencil_error_sequence_eq_endpoint_package_sequence_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    actualGraphChannelStencilErrorSequence family =
      endpointPackageStencilErrorSequence family := by
  funext n
  exact
    actual_graph_stencil_error_equals_endpoint_package_error_v0
      (family.endpoint_data n)

/-- The actual graph-action sequence inherits the endpoint-package order-h^2 bound. -/
theorem actual_graph_stencil_error_sequence_order_h2_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      (actualGraphChannelStencilErrorSequence family)
      (C / 3) := by
  simpa [actual_graph_stencil_error_sequence_eq_endpoint_package_sequence_v0 family]
    using endpoint_package_stencil_error_sequence_order_h2_bound_v0 family

/-- The actual graph-action sequence tends to zero. -/
theorem actual_graph_stencil_error_sequence_tends_to_zero_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    StencilErrorTendsToZeroFilter
      (actualGraphChannelStencilErrorSequence family) := by
  simpa [actual_graph_stencil_error_sequence_eq_endpoint_package_sequence_v0 family]
    using endpoint_package_stencil_error_sequence_tends_to_zero_v0 family

/--
Build the A1A10 contract using the actual graph-action stencil-error sequence.
-/
def uniformMeshConvergenceContractOfActualGraphStencilError
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    UniformMeshConvergenceContract where
  endpoint_package_subbranch_closed := True
  endpoint_package_subbranch_closed_supplied := True.intro
  two_sided_endpoint_package_available := True
  two_sided_endpoint_package_available_supplied := True.intro
  local_stencil_error_bound_route :=
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      (actualGraphChannelStencilErrorSequence family)
      (C / 3)
  local_stencil_error_bound_route_supplied :=
    actual_graph_stencil_error_sequence_order_h2_bound_v0 family
  global_smoothness_class := data.global_smoothness_class
  global_smoothness_class_supplied :=
    data.global_smoothness_class_supplied
  differentiability_order := data.differentiability_order
  differentiability_order_at_least_four :=
    data.differentiability_order_at_least_four
  uniform_fourth_derivative_or_remainder_bound :=
    data.uniform_fourth_derivative_or_remainder_bound
  uniform_fourth_derivative_or_remainder_bound_supplied :=
    data.uniform_fourth_derivative_or_remainder_bound_supplied
  fourth_derivative_bound := C
  fourth_derivative_bound_nonnegative :=
    (family.endpoint_data 0).fourth_derivative_bound_nonnegative
  refinement_family := concreteUniformMeshRefinementFamily
  mesh_size := concreteUniformMeshSize
  mesh_size_matches_refinement_spacing :=
    concreteUniformMeshRefinementFamily = concreteUniformMeshSize
  mesh_size_matches_refinement_spacing_supplied :=
    concrete_uniform_refinement_family_matches_mesh_v0
  mesh_size_nonnegative :=
    ∀ n : Nat, 0 ≤ concreteUniformMeshSize n
  mesh_size_nonnegative_supplied :=
    concrete_uniform_mesh_size_nonnegative_v0
  uniform_mesh_scale_condition :=
    concreteUniformMeshRefinementFamily = concreteUniformMeshSize
  uniform_mesh_scale_condition_supplied :=
    concrete_uniform_refinement_family_matches_mesh_v0
  mesh_size_tends_to_zero :=
    MeshSizeTendsToZeroFilter concreteUniformMeshSize
  mesh_size_tends_to_zero_supplied :=
    concrete_uniform_mesh_size_tends_to_zero_v0
  local_interval_model := data.local_interval_model
  local_interval_model_supplied := data.local_interval_model_supplied
  taylor_remainder_theorem := data.taylor_remainder_theorem
  taylor_remainder_theorem_supplied :=
    data.taylor_remainder_theorem_supplied
  uniform_stencil_error_bound :=
    StencilErrorTendsToZeroFilter
      (actualGraphChannelStencilErrorSequence family)
  uniform_stencil_error_bound_supplied :=
    actual_graph_stencil_error_sequence_tends_to_zero_v0 family
  continuum_second_derivative_semantics :=
    data.continuum_second_derivative_semantics
  continuum_second_derivative_semantics_supplied :=
    data.continuum_second_derivative_semantics_supplied
  continuum_laplacian_semantics :=
    data.continuum_laplacian_semantics
  continuum_laplacian_semantics_supplied :=
    data.continuum_laplacian_semantics_supplied
  sample_reconstruction_compatibility :=
    data.sample_reconstruction_compatibility
  sample_reconstruction_compatibility_supplied :=
    data.sample_reconstruction_compatibility_supplied
  operator_domain_closure := data.operator_domain_closure
  operator_domain_closure_supplied :=
    data.operator_domain_closure_supplied
  graph_laplacian_channel_relation :=
    data.graph_laplacian_channel_relation
  graph_laplacian_channel_relation_supplied :=
    data.graph_laplacian_channel_relation_supplied

/-- Build the A1A12 mode for the actual graph-action stencil-error sequence. -/
def actualGraphStencilErrorOrderH2LimitMode
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    UniformMeshOrderH2LimitMode
      (uniformMeshConvergenceContractOfActualGraphStencilError
        data family) where
  stencil_error := actualGraphChannelStencilErrorSequence family
  constant := C / 3
  constant_nonnegative :=
    endpoint_package_stencil_error_order_h2_constant_nonnegative_v0 family
  mesh_size_tends_to_zero_filter :=
    concrete_uniform_mesh_size_tends_to_zero_v0
  order_h_squared_error_bound_filter :=
    actual_graph_stencil_error_sequence_order_h2_bound_v0 family
  refinement_independent_constant := True
  refinement_independent_constant_supplied := True.intro

/-- The actual graph-action sequence constructs the A1A11 evidence object. -/
def uniformMeshConvergenceEvidenceOfActualGraphStencilError
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    UniformMeshConvergenceEvidence
      (uniformMeshConvergenceContractOfActualGraphStencilError
        data family) :=
  uniformMeshConvergenceEvidenceOfOrderH2LimitMode
    (actualGraphStencilErrorOrderH2LimitMode data family)

/-- The actual graph-action evidence has the transferred order-h^2 bound. -/
theorem actual_graph_stencil_error_evidence_order_h2_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    (uniformMeshConvergenceEvidenceOfActualGraphStencilError
        data family).order_h_squared_error_bound =
      OrderH2StencilErrorBound
        concreteUniformMeshSize
        (actualGraphChannelStencilErrorSequence family)
        (C / 3) := by
  rfl

/-- The actual graph-action evidence derives stencil-error convergence. -/
theorem actual_graph_stencil_error_evidence_derives_limit_v0
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    (uniformMeshConvergenceEvidenceOfActualGraphStencilError
        data family).stencil_error_tends_to_zero := by
  exact
    uniform_mesh_evidence_derives_stencil_error_limit
      (uniformMeshConvergenceEvidenceOfActualGraphStencilError
        data family)

/-- Remaining objects after actual graph-stencil identification. -/
inductive ActualGraphStencilErrorIdentificationObstruction where
  | noParentGraphChannelClosureReview
  | noContinuumLaplacianSemanticClosure
  | noOperatorDomainClosure
  | noRemainingA1ALiftFields
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A1A16 obstruction inventory. -/
def actualGraphStencilErrorIdentificationObstructionId :
    ActualGraphStencilErrorIdentificationObstruction -> String
  | .noParentGraphChannelClosureReview =>
      "A2A15A1A16_OBSTRUCTION_NO_PARENT_GRAPH_CHANNEL_CLOSURE_REVIEW"
  | .noContinuumLaplacianSemanticClosure =>
      "A2A15A1A16_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTIC_CLOSURE"
  | .noOperatorDomainClosure =>
      "A2A15A1A16_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noRemainingA1ALiftFields =>
      "A2A15A1A16_OBSTRUCTION_NO_REMAINING_A1A_LIFT_FIELDS"
  | .noFullA1AChannelClosure =>
      "A2A15A1A16_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction list after the A1A16 identification proof. -/
def actualGraphStencilErrorIdentificationObstructionsV0 :
    List ActualGraphStencilErrorIdentificationObstruction :=
  [ .noParentGraphChannelClosureReview
  , .noContinuumLaplacianSemanticClosure
  , .noOperatorDomainClosure
  , .noRemainingA1ALiftFields
  , .noFullA1AChannelClosure
  ]

/-- The A1A16 obstruction list is stable and explicit. -/
theorem actual_graph_stencil_error_identification_obstructions_v0_expected :
    actualGraphStencilErrorIdentificationObstructionsV0 =
      [ .noParentGraphChannelClosureReview
      , .noContinuumLaplacianSemanticClosure
      , .noOperatorDomainClosure
      , .noRemainingA1ALiftFields
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor proves the identification and records closure-review obstruction. -/
def actualGraphStencilErrorIdentificationSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The successor kind records bounded proof progress plus retained obstruction. -/
theorem actual_graph_stencil_error_identification_successor_kinds_v0_expected :
    actualGraphStencilErrorIdentificationSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A16 actual graph-stencil identification slice. -/
structure ActualGraphStencilErrorIdentificationStatus where
  actual_graph_error_object_defined : Prop
  actual_graph_error_object_defined_supplied :
    actual_graph_error_object_defined
  sampled_function_equals_endpoint_reconstruction_proved : Prop
  sampled_function_equals_endpoint_reconstruction_proved_supplied :
    sampled_function_equals_endpoint_reconstruction_proved
  actual_error_identified_with_endpoint_error_proved : Prop
  actual_error_identified_with_endpoint_error_proved_supplied :
    actual_error_identified_with_endpoint_error_proved
  actual_error_order_h2_bound_proved : Prop
  actual_error_order_h2_bound_proved_supplied :
    actual_error_order_h2_bound_proved
  actual_error_tends_to_zero_proved : Prop
  actual_error_tends_to_zero_proved_supplied :
    actual_error_tends_to_zero_proved
  a1a12_actual_mode_constructed : Prop
  a1a12_actual_mode_constructed_supplied :
    a1a12_actual_mode_constructed
  a1a11_actual_evidence_constructed : Prop
  a1a11_actual_evidence_constructed_supplied :
    a1a11_actual_evidence_constructed
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  prior_a1a15_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current A1A16 status: the actual graph-action stencil error is identified
with the endpoint-package sequence and inherits its convergence; full A1A
closure still needs a parent graph-channel closure review.
-/
def actualGraphStencilErrorIdentificationStatusV0 :
    ActualGraphStencilErrorIdentificationStatus where
  actual_graph_error_object_defined := True
  actual_graph_error_object_defined_supplied := True.intro
  sampled_function_equals_endpoint_reconstruction_proved := True
  sampled_function_equals_endpoint_reconstruction_proved_supplied := True.intro
  actual_error_identified_with_endpoint_error_proved := True
  actual_error_identified_with_endpoint_error_proved_supplied := True.intro
  actual_error_order_h2_bound_proved := True
  actual_error_order_h2_bound_proved_supplied := True.intro
  actual_error_tends_to_zero_proved := True
  actual_error_tends_to_zero_proved_supplied := True.intro
  a1a12_actual_mode_constructed := True
  a1a12_actual_mode_constructed_supplied := True.intro
  a1a11_actual_evidence_constructed := True
  a1a11_actual_evidence_constructed_supplied := True.intro
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  prior_a1a15_retained_blocker_id :=
    phase1Blocker003A2A15A1A15ActualGraphStencilErrorIdentificationRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A16GraphChannelSemanticClosureRetainedId
  outcome_id := graphLaplacianActualGraphStencilErrorIdentificationOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := actualGraphStencilErrorIdentificationSuccessorKindsV0
  obstruction_ids :=
    actualGraphStencilErrorIdentificationObstructionsV0.map
      actualGraphStencilErrorIdentificationObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def actualGraphStencilErrorIdentificationStatusReadoutV0 :
    ActualGraphStencilErrorIdentificationStatus :=
  actualGraphStencilErrorIdentificationStatusV0

/-- The actual graph-action stencil-error object is recorded. -/
theorem actual_graph_stencil_error_object_defined_v0 :
    ActualGraphStencilErrorIdentificationStatus.actual_graph_error_object_defined
      actualGraphStencilErrorIdentificationStatusReadoutV0 := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.actual_graph_error_object_defined_supplied

/-- The sampled-function reconstruction equality is recorded. -/
theorem actual_graph_stencil_error_sampled_reconstruction_proved_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.sampled_function_equals_endpoint_reconstruction_proved := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.sampled_function_equals_endpoint_reconstruction_proved_supplied

/-- The actual error equals the endpoint-package error. -/
theorem actual_graph_stencil_error_identification_proved_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.actual_error_identified_with_endpoint_error_proved := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.actual_error_identified_with_endpoint_error_proved_supplied

/-- The actual graph-action error has the order-h^2 bound. -/
theorem actual_graph_stencil_error_order_h2_proved_v0 :
    ActualGraphStencilErrorIdentificationStatus.actual_error_order_h2_bound_proved
      actualGraphStencilErrorIdentificationStatusReadoutV0 := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.actual_error_order_h2_bound_proved_supplied

/-- The actual graph-action error tends to zero. -/
theorem actual_graph_stencil_error_tends_to_zero_proved_v0 :
    ActualGraphStencilErrorIdentificationStatus.actual_error_tends_to_zero_proved
      actualGraphStencilErrorIdentificationStatusReadoutV0 := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.actual_error_tends_to_zero_proved_supplied

/-- The A1A12 actual-error mode construction is recorded. -/
theorem actual_graph_stencil_error_a1a12_mode_constructed_v0 :
    ActualGraphStencilErrorIdentificationStatus.a1a12_actual_mode_constructed
      actualGraphStencilErrorIdentificationStatusReadoutV0 := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.a1a12_actual_mode_constructed_supplied

/-- The A1A11 actual-error evidence construction is recorded. -/
theorem actual_graph_stencil_error_a1a11_evidence_constructed_v0 :
    ActualGraphStencilErrorIdentificationStatus.a1a11_actual_evidence_constructed
      actualGraphStencilErrorIdentificationStatusReadoutV0 := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.a1a11_actual_evidence_constructed_supplied

/-- A1A is not closed by the identification proof alone. -/
theorem actual_graph_stencil_error_full_a1a_not_closed_v0 :
    Not
      (ActualGraphStencilErrorIdentificationStatus.full_a1a_channel_closed
        actualGraphStencilErrorIdentificationStatusReadoutV0) := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.full_a1a_channel_not_closed

/-- The prior A1A15 retained blocker id remains exposed. -/
theorem actual_graph_stencil_error_prior_a1a15_retained_id_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.prior_a1a15_retained_blocker_id =
      phase1Blocker003A2A15A1A15ActualGraphStencilErrorIdentificationRetainedId := by
  rfl

/-- The A1A16 retained blocker id is exposed. -/
theorem actual_graph_stencil_error_retained_id_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A16GraphChannelSemanticClosureRetainedId := by
  rfl

/-- The A1A16 outcome id is exposed. -/
theorem actual_graph_stencil_error_outcome_id_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.outcome_id =
      graphLaplacianActualGraphStencilErrorIdentificationOutcomeId := by
  rfl

/-- The successor remains governed by the post-capstone anti-loop rule. -/
theorem actual_graph_stencil_error_anti_loop_rule_id_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind records proof progress plus retained obstruction. -/
theorem actual_graph_stencil_error_successor_kinds_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.successor_kinds =
      actualGraphStencilErrorIdentificationSuccessorKindsV0 := by
  rfl

/-- The retained A1A16 obstruction ids are exposed. -/
theorem actual_graph_stencil_error_obstruction_ids_v0 :
    actualGraphStencilErrorIdentificationStatusReadoutV0.obstruction_ids =
      actualGraphStencilErrorIdentificationObstructionsV0.map
        actualGraphStencilErrorIdentificationObstructionId := by
  rfl

/-- Phase 2 remains unauthorized after the A1A16 identification proof. -/
theorem actual_graph_stencil_error_phase2_not_authorized_v0 :
    Not actualGraphStencilErrorIdentificationStatusReadoutV0.phase2Authorized := by
  exact
    actualGraphStencilErrorIdentificationStatusReadoutV0
      |>.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianActualGraphStencilErrorIdentification
end QFT
end ToeFormal
