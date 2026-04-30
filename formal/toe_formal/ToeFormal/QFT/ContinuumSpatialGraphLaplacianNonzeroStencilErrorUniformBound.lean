/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound.lean

Nonzero stencil-error uniform-bound normal form for the A1A uniform mesh route.

Scope:
- reuse the concrete mesh h_n = 1 / (n + 1)
- replace the zero-error normal form with the nonzero error e_n = h_n^2
- prove the nonzero witness, order-h^2 bound, and stencil-error convergence
- construct the A1A12 mode and A1A11 evidence object for the nonzero normal
  form
- retain the theorem identifying the actual graph-Laplacian Taylor/remainder
  stencil error with this nonzero uniform-bound route
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound

open Filter
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
open ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
open scoped Topology

set_option autoImplicit false

noncomputable section

/--
Retained blocker after the nonzero normal-form proof: derive the uniform
order-h^2 bound for the actual graph-Laplacian stencil error coming from the
endpoint-package/Taylor remainder route.
-/
def phase1Blocker003A2A15A1A14NonzeroStencilErrorUniformBoundRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A14_NONZERO_STENCIL_ERROR_" ++
    "UNIFORM_BOUND_RETAINED"

/-- Outcome id for the A1A14 nonzero normal-form bound. -/
def graphLaplacianNonzeroStencilErrorUniformBoundOutcomeId : String :=
  "A2A15A1A14_NONZERO_STENCIL_ERROR_NORMAL_FORM_ORDER_H2_" ++
    "BOUND_PROVED_ACTUAL_GRAPH_ERROR_RETAINED"

/-- A concrete nonzero stencil-error normal form: `e_n = h_n^2`. -/
def concreteNonzeroUniformStencilError (n : Nat) : Real :=
  (concreteUniformMeshSize n)^2

/-- The nonzero normal-form order-h^2 constant. -/
def concreteNonzeroUniformStencilErrorConstant : Real :=
  1

/-- The nonzero stencil-error normal form is nonzero at the first index. -/
theorem concrete_nonzero_uniform_stencil_error_at_zero_v0 :
    concreteNonzeroUniformStencilError 0 = 1 := by
  norm_num [concreteNonzeroUniformStencilError, concreteUniformMeshSize]

/-- The nonzero stencil-error normal form is not identically zero. -/
theorem concrete_nonzero_uniform_stencil_error_not_zero_v0 :
    concreteNonzeroUniformStencilError 0 ≠ 0 := by
  norm_num [concrete_nonzero_uniform_stencil_error_at_zero_v0]

/-- The nonzero normal form has an eventual order-h^2 bound. -/
theorem concrete_nonzero_uniform_stencil_error_order_h2_bound_v0 :
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      concreteNonzeroUniformStencilError
      concreteNonzeroUniformStencilErrorConstant := by
  filter_upwards with n
  have hn : 0 ≤ (concreteUniformMeshSize n)^2 := sq_nonneg _
  calc
    ‖concreteNonzeroUniformStencilError n‖ =
        (concreteUniformMeshSize n)^2 := by
          rw [concreteNonzeroUniformStencilError, Real.norm_eq_abs,
            abs_of_nonneg hn]
    _ ≤ concreteNonzeroUniformStencilErrorConstant *
        (concreteUniformMeshSize n)^2 := by
          rw [concreteNonzeroUniformStencilErrorConstant, one_mul]

/-- The nonzero normal-form stencil error tends to zero. -/
theorem concrete_nonzero_uniform_stencil_error_tends_to_zero_v0 :
    StencilErrorTendsToZeroFilter concreteNonzeroUniformStencilError := by
  have hmesh_sq :
      Tendsto (fun n => (concreteUniformMeshSize n)^2) atTop (𝓝 0) := by
    simpa [MeshSizeTendsToZeroFilter] using
      concrete_uniform_mesh_size_tends_to_zero_v0.pow 2
  simpa [StencilErrorTendsToZeroFilter, concreteNonzeroUniformStencilError]
    using hmesh_sq

/--
Actual nonzero-stencil data still needed downstream of the normal-form proof.

The first field names the real graph/Taylor stencil-error sequence.  The
remaining fields are retained propositions identifying that sequence with the
normal-form bound and with the parent graph-channel semantics.
-/
structure ActualNonzeroStencilErrorRouteData where
  actual_graph_stencil_error : Nat -> Real
  endpoint_package_to_actual_error_sequence : Prop
  actual_error_sequence_matches_nonzero_normal_form : Prop
  endpoint_package_derives_uniform_order_h2_bound : Prop
  sample_reconstruction_identifies_graph_samples : Prop
  continuum_laplacian_semantics_for_actual_error : Prop
  operator_domain_closure_for_actual_error : Prop
  graph_channel_relation_for_actual_error : Prop

/--
Build the A1A10 contract using the concrete mesh and nonzero `h_n^2`
stencil-error normal form.  The semantic data remain conditional, as in A1A13.
-/
def uniformMeshConvergenceContractOfNonzeroStencilError
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshConvergenceContract where
  endpoint_package_subbranch_closed := True
  endpoint_package_subbranch_closed_supplied := True.intro
  two_sided_endpoint_package_available := True
  two_sided_endpoint_package_available_supplied := True.intro
  local_stencil_error_bound_route :=
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      concreteNonzeroUniformStencilError
      concreteNonzeroUniformStencilErrorConstant
  local_stencil_error_bound_route_supplied :=
    concrete_nonzero_uniform_stencil_error_order_h2_bound_v0
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
  fourth_derivative_bound := data.fourth_derivative_bound
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
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
    StencilErrorTendsToZeroFilter concreteNonzeroUniformStencilError
  uniform_stencil_error_bound_supplied :=
    concrete_nonzero_uniform_stencil_error_tends_to_zero_v0
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

/-- The nonzero contract exposes the concrete mesh size. -/
theorem nonzero_stencil_error_contract_mesh_size_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceContractOfNonzeroStencilError data).mesh_size =
      concreteUniformMeshSize := by
  rfl

/-- The nonzero contract exposes the concrete nonzero stencil-error convergence field. -/
theorem nonzero_stencil_error_contract_uniform_error_bound_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceContractOfNonzeroStencilError data).uniform_stencil_error_bound =
      StencilErrorTendsToZeroFilter concreteNonzeroUniformStencilError := by
  rfl

/-- Build the A1A12 mode for the nonzero stencil-error normal form. -/
def nonzeroStencilErrorOrderH2LimitMode
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshOrderH2LimitMode
      (uniformMeshConvergenceContractOfNonzeroStencilError data) where
  stencil_error := concreteNonzeroUniformStencilError
  constant := concreteNonzeroUniformStencilErrorConstant
  constant_nonnegative := by
    rw [concreteNonzeroUniformStencilErrorConstant]
    exact zero_le_one
  mesh_size_tends_to_zero_filter :=
    concrete_uniform_mesh_size_tends_to_zero_v0
  order_h_squared_error_bound_filter :=
    concrete_nonzero_uniform_stencil_error_order_h2_bound_v0
  refinement_independent_constant := True
  refinement_independent_constant_supplied := True.intro

/--
The nonzero stencil-error normal form constructs the A1A11 evidence object
through the A1A12 order-h^2 bridge.
-/
def uniformMeshConvergenceEvidenceOfNonzeroStencilError
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshConvergenceEvidence
      (uniformMeshConvergenceContractOfNonzeroStencilError data) :=
  uniformMeshConvergenceEvidenceOfOrderH2LimitMode
    (nonzeroStencilErrorOrderH2LimitMode data)

/-- The nonzero evidence has the concrete order-h^2 bound field. -/
theorem nonzero_stencil_error_evidence_order_h2_bound_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceEvidenceOfNonzeroStencilError data).order_h_squared_error_bound =
      OrderH2StencilErrorBound
        concreteUniformMeshSize
        concreteNonzeroUniformStencilError
        concreteNonzeroUniformStencilErrorConstant := by
  rfl

/-- The nonzero evidence derives the concrete stencil-error convergence field. -/
theorem nonzero_stencil_error_evidence_derives_stencil_error_limit_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceEvidenceOfNonzeroStencilError data).stencil_error_tends_to_zero := by
  exact
    uniform_mesh_evidence_derives_stencil_error_limit
      (uniformMeshConvergenceEvidenceOfNonzeroStencilError data)

/-- Remaining objects after the nonzero normal-form uniform-bound proof. -/
inductive NonzeroStencilErrorUniformBoundObstruction where
  | noActualGraphStencilErrorSequence
  | noEndpointPackageToActualErrorSequence
  | noActualErrorMatchesNonzeroNormalForm
  | noEndpointPackageToUniformOrderH2Bound
  | noSampleReconstructionCompatibilityForActualError
  | noContinuumLaplacianSemanticsForActualError
  | noOperatorDomainClosureForActualError
  | noGraphChannelRelationForActualError
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A1A14 obstruction inventory. -/
def nonzeroStencilErrorUniformBoundObstructionId :
    NonzeroStencilErrorUniformBoundObstruction -> String
  | .noActualGraphStencilErrorSequence =>
      "A2A15A1A14_OBSTRUCTION_NO_ACTUAL_GRAPH_STENCIL_ERROR_SEQUENCE"
  | .noEndpointPackageToActualErrorSequence =>
      "A2A15A1A14_OBSTRUCTION_NO_ENDPOINT_PACKAGE_TO_ACTUAL_ERROR_SEQUENCE"
  | .noActualErrorMatchesNonzeroNormalForm =>
      "A2A15A1A14_OBSTRUCTION_NO_ACTUAL_ERROR_MATCHES_NONZERO_NORMAL_FORM"
  | .noEndpointPackageToUniformOrderH2Bound =>
      "A2A15A1A14_OBSTRUCTION_NO_ENDPOINT_PACKAGE_TO_UNIFORM_ORDER_H2_BOUND"
  | .noSampleReconstructionCompatibilityForActualError =>
      "A2A15A1A14_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_FOR_ACTUAL_ERROR"
  | .noContinuumLaplacianSemanticsForActualError =>
      "A2A15A1A14_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS_FOR_ACTUAL_ERROR"
  | .noOperatorDomainClosureForActualError =>
      "A2A15A1A14_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FOR_ACTUAL_ERROR"
  | .noGraphChannelRelationForActualError =>
      "A2A15A1A14_OBSTRUCTION_NO_GRAPH_CHANNEL_RELATION_FOR_ACTUAL_ERROR"
  | .noFullA1AChannelClosure =>
      "A2A15A1A14_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction list after the A1A14 nonzero normal-form proof. -/
def nonzeroStencilErrorUniformBoundObstructionsV0 :
    List NonzeroStencilErrorUniformBoundObstruction :=
  [ .noActualGraphStencilErrorSequence
  , .noEndpointPackageToActualErrorSequence
  , .noActualErrorMatchesNonzeroNormalForm
  , .noEndpointPackageToUniformOrderH2Bound
  , .noSampleReconstructionCompatibilityForActualError
  , .noContinuumLaplacianSemanticsForActualError
  , .noOperatorDomainClosureForActualError
  , .noGraphChannelRelationForActualError
  , .noFullA1AChannelClosure
  ]

/-- The A1A14 obstruction list is stable and explicit. -/
theorem nonzero_stencil_error_uniform_bound_obstructions_v0_expected :
    nonzeroStencilErrorUniformBoundObstructionsV0 =
      [ .noActualGraphStencilErrorSequence
      , .noEndpointPackageToActualErrorSequence
      , .noActualErrorMatchesNonzeroNormalForm
      , .noEndpointPackageToUniformOrderH2Bound
      , .noSampleReconstructionCompatibilityForActualError
      , .noContinuumLaplacianSemanticsForActualError
      , .noOperatorDomainClosureForActualError
      , .noGraphChannelRelationForActualError
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor proves a nonzero bound normal form and records obstruction. -/
def nonzeroStencilErrorUniformBoundSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The successor kind records bounded proof progress plus retained obstruction. -/
theorem nonzero_stencil_error_uniform_bound_successor_kinds_v0_expected :
    nonzeroStencilErrorUniformBoundSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A14 nonzero stencil-error uniform-bound slice. -/
structure NonzeroStencilErrorUniformBoundStatus where
  nonzero_error_sequence_defined : Prop
  nonzero_error_sequence_defined_supplied :
    nonzero_error_sequence_defined
  nonzero_witness_proved : Prop
  nonzero_witness_proved_supplied : nonzero_witness_proved
  order_h2_uniform_bound_proved : Prop
  order_h2_uniform_bound_proved_supplied :
    order_h2_uniform_bound_proved
  stencil_error_tends_to_zero_proved : Prop
  stencil_error_tends_to_zero_proved_supplied :
    stencil_error_tends_to_zero_proved
  a1a12_nonzero_mode_constructed : Prop
  a1a12_nonzero_mode_constructed_supplied :
    a1a12_nonzero_mode_constructed
  a1a11_nonzero_evidence_constructed : Prop
  a1a11_nonzero_evidence_constructed_supplied :
    a1a11_nonzero_evidence_constructed
  actual_graph_stencil_error_bound_proved : Prop
  actual_graph_stencil_error_bound_not_proved :
    Not actual_graph_stencil_error_bound_proved
  graph_channel_relation_for_actual_error_proved : Prop
  graph_channel_relation_for_actual_error_not_proved :
    Not graph_channel_relation_for_actual_error_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  prior_a1a13_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current A1A14 status: the nonzero normal-form bound is theorem-backed, while
the actual endpoint/Taylor graph-stencil uniform bound remains retained.
-/
def nonzeroStencilErrorUniformBoundStatusV0 :
    NonzeroStencilErrorUniformBoundStatus where
  nonzero_error_sequence_defined := True
  nonzero_error_sequence_defined_supplied := True.intro
  nonzero_witness_proved := True
  nonzero_witness_proved_supplied := True.intro
  order_h2_uniform_bound_proved := True
  order_h2_uniform_bound_proved_supplied := True.intro
  stencil_error_tends_to_zero_proved := True
  stencil_error_tends_to_zero_proved_supplied := True.intro
  a1a12_nonzero_mode_constructed := True
  a1a12_nonzero_mode_constructed_supplied := True.intro
  a1a11_nonzero_evidence_constructed := True
  a1a11_nonzero_evidence_constructed_supplied := True.intro
  actual_graph_stencil_error_bound_proved := False
  actual_graph_stencil_error_bound_not_proved := by
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
  prior_a1a13_retained_blocker_id :=
    phase1Blocker003A2A15A1A13ConcreteUniformMeshInstantiationRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A14NonzeroStencilErrorUniformBoundRetainedId
  outcome_id := graphLaplacianNonzeroStencilErrorUniformBoundOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := nonzeroStencilErrorUniformBoundSuccessorKindsV0
  obstruction_ids :=
    nonzeroStencilErrorUniformBoundObstructionsV0.map
      nonzeroStencilErrorUniformBoundObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def nonzeroStencilErrorUniformBoundStatusReadoutV0 :
    NonzeroStencilErrorUniformBoundStatus :=
  nonzeroStencilErrorUniformBoundStatusV0

/-- The nonzero error sequence is recorded. -/
theorem nonzero_stencil_error_sequence_defined_v0 :
    NonzeroStencilErrorUniformBoundStatus.nonzero_error_sequence_defined
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.nonzero_error_sequence_defined_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The nonzero witness is recorded as proved. -/
theorem nonzero_stencil_error_witness_proved_v0 :
    NonzeroStencilErrorUniformBoundStatus.nonzero_witness_proved
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.nonzero_witness_proved_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The order-h^2 uniform bound is recorded as proved for the normal form. -/
theorem nonzero_stencil_error_order_h2_bound_proved_v0 :
    NonzeroStencilErrorUniformBoundStatus.order_h2_uniform_bound_proved
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.order_h2_uniform_bound_proved_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The nonzero stencil-error convergence is recorded as proved. -/
theorem nonzero_stencil_error_tends_to_zero_proved_v0 :
    NonzeroStencilErrorUniformBoundStatus.stencil_error_tends_to_zero_proved
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.stencil_error_tends_to_zero_proved_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The A1A12 nonzero mode construction is recorded. -/
theorem nonzero_stencil_error_a1a12_mode_constructed_v0 :
    NonzeroStencilErrorUniformBoundStatus.a1a12_nonzero_mode_constructed
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.a1a12_nonzero_mode_constructed_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The A1A11 nonzero evidence construction is recorded. -/
theorem nonzero_stencil_error_a1a11_evidence_constructed_v0 :
    NonzeroStencilErrorUniformBoundStatus.a1a11_nonzero_evidence_constructed
      nonzeroStencilErrorUniformBoundStatusReadoutV0 := by
  exact
    NonzeroStencilErrorUniformBoundStatus.a1a11_nonzero_evidence_constructed_supplied
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The actual graph-stencil uniform bound remains retained. -/
theorem nonzero_stencil_error_actual_graph_bound_not_proved_v0 :
    Not
      (NonzeroStencilErrorUniformBoundStatus.actual_graph_stencil_error_bound_proved
        nonzeroStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    NonzeroStencilErrorUniformBoundStatus.actual_graph_stencil_error_bound_not_proved
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The graph-channel relation for actual stencil error remains retained. -/
theorem nonzero_stencil_error_graph_relation_not_proved_v0 :
    Not
      (NonzeroStencilErrorUniformBoundStatus.graph_channel_relation_for_actual_error_proved
        nonzeroStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    NonzeroStencilErrorUniformBoundStatus.graph_channel_relation_for_actual_error_not_proved
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- A1A is not closed by the A1A14 nonzero normal-form proof. -/
theorem nonzero_stencil_error_full_a1a_not_closed_v0 :
    Not
      (NonzeroStencilErrorUniformBoundStatus.full_a1a_channel_closed
        nonzeroStencilErrorUniformBoundStatusReadoutV0) := by
  exact
    NonzeroStencilErrorUniformBoundStatus.full_a1a_channel_not_closed
      nonzeroStencilErrorUniformBoundStatusReadoutV0

/-- The prior A1A13 retained blocker id remains exposed. -/
theorem nonzero_stencil_error_prior_a1a13_retained_id_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.prior_a1a13_retained_blocker_id =
      phase1Blocker003A2A15A1A13ConcreteUniformMeshInstantiationRetainedId := by
  rfl

/-- The A1A14 retained blocker id is exposed. -/
theorem nonzero_stencil_error_retained_id_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A14NonzeroStencilErrorUniformBoundRetainedId := by
  rfl

/-- The A1A14 outcome id is exposed. -/
theorem nonzero_stencil_error_outcome_id_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.outcome_id =
      graphLaplacianNonzeroStencilErrorUniformBoundOutcomeId := by
  rfl

/-- The successor remains governed by the post-capstone anti-loop rule. -/
theorem nonzero_stencil_error_anti_loop_rule_id_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind records bounded proof progress plus retained obstruction. -/
theorem nonzero_stencil_error_successor_kinds_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.successor_kinds =
      nonzeroStencilErrorUniformBoundSuccessorKindsV0 := by
  rfl

/-- The retained A1A14 obstruction ids are exposed. -/
theorem nonzero_stencil_error_obstruction_ids_v0 :
    nonzeroStencilErrorUniformBoundStatusReadoutV0.obstruction_ids =
      nonzeroStencilErrorUniformBoundObstructionsV0.map
        nonzeroStencilErrorUniformBoundObstructionId := by
  rfl

/-- Phase 2 remains unauthorized after the A1A14 normal-form proof. -/
theorem nonzero_stencil_error_phase2_not_authorized_v0 :
    Not nonzeroStencilErrorUniformBoundStatusReadoutV0.phase2Authorized := by
  exact nonzeroStencilErrorUniformBoundStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianNonzeroStencilErrorUniformBound
end QFT
end ToeFormal
