/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound.lean

Endpoint-package stencil-error uniform bound for the A1A graph-Laplacian route.

Scope:
- define the local stencil-error value produced by the two-sided endpoint
  package
- lift a refinement-indexed family of endpoint packages to a concrete
  stencil-error sequence
- prove the sequence has an order-h^2 bound and tends to zero
- construct the A1A12 mode and A1A11 evidence object for this endpoint-package
  stencil-error sequence
- retain the theorem identifying this endpoint-package sequence with the
  actual graph-Laplacian action and its parent graph-channel semantics
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound

open Filter
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge
open ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
open ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
open ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound
open scoped Topology

set_option autoImplicit false

noncomputable section

/--
Retained blocker after the endpoint-package uniform-bound proof: identify the
endpoint-package stencil-error sequence with the actual graph-Laplacian action
and prove the parent graph-channel semantics.
-/
def phase1Blocker003A2A15A1A15ActualGraphStencilErrorIdentificationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A15_ACTUAL_GRAPH_STENCIL_ERROR_" ++
    "IDENTIFICATION_RETAINED"

/-- Outcome id for the A1A15 endpoint-package stencil-error uniform bound. -/
def graphLaplacianEndpointPackageStencilErrorUniformBoundOutcomeId : String :=
  "A2A15A1A15_ENDPOINT_PACKAGE_STENCIL_ERROR_ORDER_H2_BOUND_" ++
    "PROVED_GRAPH_IDENTIFICATION_RETAINED"

/--
The scalar local stencil-error value obtained from the constructed two-sided
endpoint package.
-/
def endpointPackageStencilErrorOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    Real :=
  centeredScaledGraphLaplacianAtCenter h
      (sampledQuadraticCubicRemainderField
        ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)
        (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).first_derivative
        (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).value
        ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).third_derivative / 6)
        h
        (symmetricTaylorBridgeRemainderField
          (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data))) -
    quadraticContinuumSecondDerivative
      ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)

/-- The two-sided endpoint package bounds its local stencil-error value. -/
theorem endpoint_package_stencil_error_abs_bound_v0
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    |endpointPackageStencilErrorOfGlobalCenteredAlignmentData data| ≤
      fourthDerivativeStencilTolerance (4 * C) h := by
  simpa [endpointPackageStencilErrorOfGlobalCenteredAlignmentData] using
    two_sided_endpoint_package_feeds_local_stencil_error_bound
      h_nonzero refinementParameter refinementParameterPositive data

/--
A refinement-indexed family of two-sided endpoint packages over the concrete
mesh `h_n = 1 / (n + 1)`.
-/
structure EndpointPackageStencilErrorFamilyData
    (f : Real -> Real)
    (x C : Real) where
  endpoint_data :
    ∀ n : Nat,
      EndpointPackageDerivationWithGlobalCenteredAlignmentData
        f x (concreteUniformMeshSize n) C
  refinement_parameter : Nat
  refinement_parameter_positive : 0 < refinement_parameter

/-- The endpoint-package local stencil-error sequence over the concrete mesh. -/
def endpointPackageStencilErrorSequence
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    Nat -> Real :=
  fun n =>
    endpointPackageStencilErrorOfGlobalCenteredAlignmentData
      (family.endpoint_data n)

/-- Each endpoint-package sequence value has the local fourth-derivative bound. -/
theorem endpoint_package_stencil_error_sequence_abs_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C)
    (n : Nat) :
    |endpointPackageStencilErrorSequence family n| ≤
      fourthDerivativeStencilTolerance (4 * C)
        (concreteUniformMeshSize n) := by
  have h_ne : concreteUniformMeshSize n ≠ 0 := by
    exact ne_of_gt (family.endpoint_data n).h_positive
  have h_nonzero :
      concreteUniformMeshSize n * concreteUniformMeshSize n ≠ 0 := by
    exact mul_ne_zero h_ne h_ne
  exact
    endpoint_package_stencil_error_abs_bound_v0
      h_nonzero
      family.refinement_parameter
      family.refinement_parameter_positive
      (family.endpoint_data n)

/--
The endpoint-package stencil-error sequence has a refinement-independent
order-h^2 bound.
-/
theorem endpoint_package_stencil_error_sequence_order_h2_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      (endpointPackageStencilErrorSequence family)
      (C / 3) := by
  filter_upwards with n
  have hlocal :=
    endpoint_package_stencil_error_sequence_abs_bound_v0 family n
  calc
    ‖endpointPackageStencilErrorSequence family n‖ =
        |endpointPackageStencilErrorSequence family n| := by
          rw [Real.norm_eq_abs]
    _ ≤ fourthDerivativeStencilTolerance (4 * C)
        (concreteUniformMeshSize n) := hlocal
    _ = (C / 3) * (concreteUniformMeshSize n)^2 := by
        unfold fourthDerivativeStencilTolerance
        ring

/-- The endpoint-package order-h^2 constant is nonnegative. -/
theorem endpoint_package_stencil_error_order_h2_constant_nonnegative_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    0 ≤ C / 3 := by
  exact
    div_nonneg
      (family.endpoint_data 0).fourth_derivative_bound_nonnegative
      (by norm_num)

/-- The endpoint-package stencil-error sequence tends to zero. -/
theorem endpoint_package_stencil_error_sequence_tends_to_zero_v0
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    StencilErrorTendsToZeroFilter
      (endpointPackageStencilErrorSequence family) := by
  have hmesh_sq :
      Tendsto (fun n => (concreteUniformMeshSize n)^2) atTop (𝓝 0) := by
    simpa [MeshSizeTendsToZeroFilter] using
      concrete_uniform_mesh_size_tends_to_zero_v0.pow 2
  have hbound :
      Tendsto
        (fun n => (C / 3) * (concreteUniformMeshSize n)^2)
        atTop
        (𝓝 0) := by
    simpa using hmesh_sq.const_mul (C / 3)
  exact
    squeeze_zero_norm'
      (endpoint_package_stencil_error_sequence_order_h2_bound_v0 family)
      hbound

/--
Build the A1A10 contract using the endpoint-package stencil-error sequence
instead of the prior zero or `h_n^2` normal forms.
-/
def uniformMeshConvergenceContractOfEndpointPackageStencilError
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
      (endpointPackageStencilErrorSequence family)
      (C / 3)
  local_stencil_error_bound_route_supplied :=
    endpoint_package_stencil_error_sequence_order_h2_bound_v0 family
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
      (endpointPackageStencilErrorSequence family)
  uniform_stencil_error_bound_supplied :=
    endpoint_package_stencil_error_sequence_tends_to_zero_v0 family
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

/-- The endpoint-package contract exposes the concrete endpoint error sequence. -/
theorem endpoint_package_stencil_error_contract_uniform_error_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    (uniformMeshConvergenceContractOfEndpointPackageStencilError
        data family).uniform_stencil_error_bound =
      StencilErrorTendsToZeroFilter
        (endpointPackageStencilErrorSequence family) := by
  rfl

/-- Build the A1A12 mode for the endpoint-package stencil-error sequence. -/
def endpointPackageStencilErrorOrderH2LimitMode
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    UniformMeshOrderH2LimitMode
      (uniformMeshConvergenceContractOfEndpointPackageStencilError
        data family) where
  stencil_error := endpointPackageStencilErrorSequence family
  constant := C / 3
  constant_nonnegative :=
    endpoint_package_stencil_error_order_h2_constant_nonnegative_v0 family
  mesh_size_tends_to_zero_filter :=
    concrete_uniform_mesh_size_tends_to_zero_v0
  order_h_squared_error_bound_filter :=
    endpoint_package_stencil_error_sequence_order_h2_bound_v0 family
  refinement_independent_constant := True
  refinement_independent_constant_supplied := True.intro

/--
The endpoint-package stencil-error sequence constructs the A1A11 evidence
object through the A1A12 order-h^2 bridge.
-/
def uniformMeshConvergenceEvidenceOfEndpointPackageStencilError
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    UniformMeshConvergenceEvidence
      (uniformMeshConvergenceContractOfEndpointPackageStencilError
        data family) :=
  uniformMeshConvergenceEvidenceOfOrderH2LimitMode
    (endpointPackageStencilErrorOrderH2LimitMode data family)

/-- The endpoint-package evidence has the derived order-h^2 bound field. -/
theorem endpoint_package_stencil_error_evidence_order_h2_bound_v0
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    (uniformMeshConvergenceEvidenceOfEndpointPackageStencilError
        data family).order_h_squared_error_bound =
      OrderH2StencilErrorBound
        concreteUniformMeshSize
        (endpointPackageStencilErrorSequence family)
        (C / 3) := by
  rfl

/-- The endpoint-package evidence derives stencil-error convergence. -/
theorem endpoint_package_stencil_error_evidence_derives_limit_v0
    {f : Real -> Real}
    {x C : Real}
    (data : ConcreteUniformMeshSemanticData)
    (family : EndpointPackageStencilErrorFamilyData f x C) :
    (uniformMeshConvergenceEvidenceOfEndpointPackageStencilError
        data family).stencil_error_tends_to_zero := by
  exact
    uniform_mesh_evidence_derives_stencil_error_limit
      (uniformMeshConvergenceEvidenceOfEndpointPackageStencilError
        data family)

/--
Route data still needed to identify the endpoint-package sequence with the
actual graph-Laplacian action and parent graph-channel semantics.
-/
structure EndpointPackageToActualGraphStencilRouteData
    {f : Real -> Real}
    {x C : Real}
    (family : EndpointPackageStencilErrorFamilyData f x C) where
  actual_graph_stencil_error : Nat -> Real
  endpoint_error_matches_actual_graph_error :
    endpointPackageStencilErrorSequence family =
      actual_graph_stencil_error
  sample_reconstruction_identifies_graph_samples : Prop
  sample_reconstruction_identifies_graph_samples_supplied :
    sample_reconstruction_identifies_graph_samples
  continuum_laplacian_semantics_for_actual_error : Prop
  continuum_laplacian_semantics_for_actual_error_supplied :
    continuum_laplacian_semantics_for_actual_error
  operator_domain_closure_for_actual_error : Prop
  operator_domain_closure_for_actual_error_supplied :
    operator_domain_closure_for_actual_error
  graph_channel_relation_for_actual_error : Prop
  graph_channel_relation_for_actual_error_supplied :
    graph_channel_relation_for_actual_error

/-- Route data identifies the endpoint-package error sequence with graph error. -/
theorem endpoint_package_route_identifies_actual_graph_error_v0
    {f : Real -> Real}
    {x C : Real}
    {family : EndpointPackageStencilErrorFamilyData f x C}
    (route : EndpointPackageToActualGraphStencilRouteData family) :
    endpointPackageStencilErrorSequence family =
      route.actual_graph_stencil_error := by
  exact route.endpoint_error_matches_actual_graph_error

/-- Remaining objects after the endpoint-package uniform-bound proof. -/
inductive EndpointPackageStencilErrorUniformBoundObstruction where
  | noActualGraphStencilErrorIdentification
  | noGraphSamplingIdentification
  | noContinuumLaplacianSemanticsForActualError
  | noOperatorDomainClosureForActualError
  | noGraphChannelRelationForActualError
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A1A15 obstruction inventory. -/
def endpointPackageStencilErrorUniformBoundObstructionId :
    EndpointPackageStencilErrorUniformBoundObstruction -> String
  | .noActualGraphStencilErrorIdentification =>
      "A2A15A1A15_OBSTRUCTION_NO_ACTUAL_GRAPH_STENCIL_ERROR_IDENTIFICATION"
  | .noGraphSamplingIdentification =>
      "A2A15A1A15_OBSTRUCTION_NO_GRAPH_SAMPLING_IDENTIFICATION"
  | .noContinuumLaplacianSemanticsForActualError =>
      "A2A15A1A15_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS_FOR_ACTUAL_ERROR"
  | .noOperatorDomainClosureForActualError =>
      "A2A15A1A15_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FOR_ACTUAL_ERROR"
  | .noGraphChannelRelationForActualError =>
      "A2A15A1A15_OBSTRUCTION_NO_GRAPH_CHANNEL_RELATION_FOR_ACTUAL_ERROR"
  | .noFullA1AChannelClosure =>
      "A2A15A1A15_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction list after the A1A15 endpoint-package bound proof. -/
def endpointPackageStencilErrorUniformBoundObstructionsV0 :
    List EndpointPackageStencilErrorUniformBoundObstruction :=
  [ .noActualGraphStencilErrorIdentification
  , .noGraphSamplingIdentification
  , .noContinuumLaplacianSemanticsForActualError
  , .noOperatorDomainClosureForActualError
  , .noGraphChannelRelationForActualError
  , .noFullA1AChannelClosure
  ]

/-- The A1A15 obstruction list is stable and explicit. -/
theorem endpoint_package_stencil_error_obstructions_v0_expected :
    endpointPackageStencilErrorUniformBoundObstructionsV0 =
      [ .noActualGraphStencilErrorIdentification
      , .noGraphSamplingIdentification
      , .noContinuumLaplacianSemanticsForActualError
      , .noOperatorDomainClosureForActualError
      , .noGraphChannelRelationForActualError
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor proves the endpoint-package bound and records obstruction. -/
def endpointPackageStencilErrorUniformBoundSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The successor kind records bounded proof progress plus retained obstruction. -/
theorem endpoint_package_stencil_error_successor_kinds_v0_expected :
    endpointPackageStencilErrorUniformBoundSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A15 endpoint-package uniform-bound slice. -/
structure EndpointPackageStencilErrorUniformBoundStatus where
  endpoint_error_sequence_defined : Prop
  endpoint_error_sequence_defined_supplied :
    endpoint_error_sequence_defined
  endpoint_package_to_local_error_bound_proved : Prop
  endpoint_package_to_local_error_bound_proved_supplied :
    endpoint_package_to_local_error_bound_proved
  endpoint_error_order_h2_bound_proved : Prop
  endpoint_error_order_h2_bound_proved_supplied :
    endpoint_error_order_h2_bound_proved
  endpoint_error_tends_to_zero_proved : Prop
  endpoint_error_tends_to_zero_proved_supplied :
    endpoint_error_tends_to_zero_proved
  a1a12_endpoint_mode_constructed : Prop
  a1a12_endpoint_mode_constructed_supplied :
    a1a12_endpoint_mode_constructed
  a1a11_endpoint_evidence_constructed : Prop
  a1a11_endpoint_evidence_constructed_supplied :
    a1a11_endpoint_evidence_constructed
  endpoint_error_identified_as_graph_action : Prop
  endpoint_error_identified_as_graph_action_not_proved :
    Not endpoint_error_identified_as_graph_action
  graph_channel_relation_for_actual_error_proved : Prop
  graph_channel_relation_for_actual_error_not_proved :
    Not graph_channel_relation_for_actual_error_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  prior_a1a14_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current A1A15 status: endpoint-package stencil-error convergence is
theorem-backed, while graph-action identification and parent semantics remain
retained.
-/
def endpointPackageStencilErrorUniformBoundStatusV0 :
    EndpointPackageStencilErrorUniformBoundStatus where
  endpoint_error_sequence_defined := True
  endpoint_error_sequence_defined_supplied := True.intro
  endpoint_package_to_local_error_bound_proved := True
  endpoint_package_to_local_error_bound_proved_supplied := True.intro
  endpoint_error_order_h2_bound_proved := True
  endpoint_error_order_h2_bound_proved_supplied := True.intro
  endpoint_error_tends_to_zero_proved := True
  endpoint_error_tends_to_zero_proved_supplied := True.intro
  a1a12_endpoint_mode_constructed := True
  a1a12_endpoint_mode_constructed_supplied := True.intro
  a1a11_endpoint_evidence_constructed := True
  a1a11_endpoint_evidence_constructed_supplied := True.intro
  endpoint_error_identified_as_graph_action := False
  endpoint_error_identified_as_graph_action_not_proved := by
    intro h
    exact h
  graph_channel_relation_for_actual_error_proved := False
  graph_channel_relation_for_actual_error_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  prior_a1a14_retained_blocker_id :=
    phase1Blocker003A2A15A1A14NonzeroStencilErrorUniformBoundRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A15ActualGraphStencilErrorIdentificationRetainedId
  outcome_id := graphLaplacianEndpointPackageStencilErrorUniformBoundOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointPackageStencilErrorUniformBoundSuccessorKindsV0
  obstruction_ids :=
    endpointPackageStencilErrorUniformBoundObstructionsV0.map
      endpointPackageStencilErrorUniformBoundObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def endpointPackageStencilErrorUniformBoundStatusReadoutV0 :
    EndpointPackageStencilErrorUniformBoundStatus :=
  endpointPackageStencilErrorUniformBoundStatusV0

/-- The endpoint-package stencil-error sequence is recorded. -/
theorem endpoint_package_stencil_error_sequence_defined_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.endpoint_error_sequence_defined
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.endpoint_error_sequence_defined_supplied

/-- The endpoint package bounds the local stencil-error value. -/
theorem endpoint_package_stencil_error_local_bound_proved_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.endpoint_package_to_local_error_bound_proved
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.endpoint_package_to_local_error_bound_proved_supplied

/-- The endpoint-package stencil-error sequence has an order-h^2 bound. -/
theorem endpoint_package_stencil_error_order_h2_bound_proved_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.endpoint_error_order_h2_bound_proved
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.endpoint_error_order_h2_bound_proved_supplied

/-- The endpoint-package stencil-error sequence tends to zero. -/
theorem endpoint_package_stencil_error_tends_to_zero_proved_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.endpoint_error_tends_to_zero_proved
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.endpoint_error_tends_to_zero_proved_supplied

/-- The A1A12 endpoint-package mode construction is recorded. -/
theorem endpoint_package_stencil_error_a1a12_mode_constructed_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.a1a12_endpoint_mode_constructed
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.a1a12_endpoint_mode_constructed_supplied

/-- The A1A11 endpoint-package evidence construction is recorded. -/
theorem endpoint_package_stencil_error_a1a11_evidence_constructed_v0 :
    EndpointPackageStencilErrorUniformBoundStatus.a1a11_endpoint_evidence_constructed
      endpointPackageStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.a1a11_endpoint_evidence_constructed_supplied

/-- The graph-action identification remains retained. -/
theorem endpoint_package_stencil_error_graph_action_not_identified_v0 :
    Not
      (EndpointPackageStencilErrorUniformBoundStatus.endpoint_error_identified_as_graph_action
        endpointPackageStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.endpoint_error_identified_as_graph_action_not_proved

/-- The graph-channel relation for the actual error remains retained. -/
theorem endpoint_package_stencil_error_graph_relation_not_proved_v0 :
    Not
      (EndpointPackageStencilErrorUniformBoundStatus.graph_channel_relation_for_actual_error_proved
        endpointPackageStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.graph_channel_relation_for_actual_error_not_proved

/-- A1A is not closed by the endpoint-package stencil-error bound. -/
theorem endpoint_package_stencil_error_full_a1a_not_closed_v0 :
    Not
      (EndpointPackageStencilErrorUniformBoundStatus.full_a1a_channel_closed
        endpointPackageStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.full_a1a_channel_not_closed

/-- The prior A1A14 retained blocker id remains exposed. -/
theorem endpoint_package_stencil_error_prior_a1a14_retained_id_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.prior_a1a14_retained_blocker_id =
      phase1Blocker003A2A15A1A14NonzeroStencilErrorUniformBoundRetainedId := by
  rfl

/-- The A1A15 retained blocker id is exposed. -/
theorem endpoint_package_stencil_error_retained_id_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A15ActualGraphStencilErrorIdentificationRetainedId := by
  rfl

/-- The A1A15 outcome id is exposed. -/
theorem endpoint_package_stencil_error_outcome_id_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.outcome_id =
      graphLaplacianEndpointPackageStencilErrorUniformBoundOutcomeId := by
  rfl

/-- The successor remains governed by the post-capstone anti-loop rule. -/
theorem endpoint_package_stencil_error_anti_loop_rule_id_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind records proof progress plus retained obstruction. -/
theorem endpoint_package_stencil_error_successor_kinds_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.successor_kinds =
      endpointPackageStencilErrorUniformBoundSuccessorKindsV0 := by
  rfl

/-- The retained A1A15 obstruction ids are exposed. -/
theorem endpoint_package_stencil_error_obstruction_ids_v0 :
    endpointPackageStencilErrorUniformBoundStatusReadoutV0.obstruction_ids =
      endpointPackageStencilErrorUniformBoundObstructionsV0.map
        endpointPackageStencilErrorUniformBoundObstructionId := by
  rfl

/-- Phase 2 remains unauthorized after the A1A15 endpoint-package bound. -/
theorem endpoint_package_stencil_error_phase2_not_authorized_v0 :
    Not
      endpointPackageStencilErrorUniformBoundStatusReadoutV0.phase2Authorized := by
  exact
    endpointPackageStencilErrorUniformBoundStatusReadoutV0
      |>.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound
end QFT
end ToeFormal
