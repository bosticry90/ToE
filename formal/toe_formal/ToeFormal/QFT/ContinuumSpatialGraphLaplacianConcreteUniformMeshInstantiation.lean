/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation.lean

Concrete mesh instantiation attempt for the A1A uniform mesh route.

Scope:
- instantiate the chosen real-filter mesh with h_n = 1 / (n + 1)
- instantiate a concrete zero stencil-error sequence
- prove mesh-to-zero, mesh nonnegativity, order-h^2 error control, and
  zero-error convergence
- build the A1A12 mode and A1A11 evidence object for this concrete
  mesh/error normal form
- retain the semantic graph-channel derivation from endpoint-package data,
  sample/reconstruction compatibility, continuum Laplacian semantics, and
  operator-domain closure
-/

import Mathlib.Analysis.SpecificLimits.Basic
import ToeFormal.QFT.ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation

open Filter
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
open scoped Topology

set_option autoImplicit false

noncomputable section

/--
Retained blocker after the concrete mesh/zero-error normal form: derive this
mode from the actual graph-Laplacian refinement channel, not just from a
selected mesh/error sequence.
-/
def phase1Blocker003A2A15A1A13ConcreteUniformMeshInstantiationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A13_CONCRETE_UNIFORM_MESH_" ++
    "INSTANTIATION_RETAINED"

/-- Outcome id for the A1A13 concrete mesh instantiation attempt. -/
def graphLaplacianConcreteUniformMeshInstantiationOutcomeId : String :=
  "A2A15A1A13_CONCRETE_MESH_ZERO_ERROR_MODE_INSTANTIATED_" ++
    "GRAPH_CHANNEL_RETAINED"

/-- A concrete refinement family with mesh size `1 / (n + 1)`. -/
def concreteUniformMeshRefinementFamily (n : Nat) : Real :=
  ((n : Real) + 1)⁻¹

/-- The concrete mesh size used by the A1A13 normal form. -/
def concreteUniformMeshSize (n : Nat) : Real :=
  ((n : Real) + 1)⁻¹

/-- Concrete zero stencil-error sequence for the bounded A1A13 normal form. -/
def concreteUniformMeshStencilError (_n : Nat) : Real :=
  0

/-- The order-h^2 constant for the zero-error normal form. -/
def concreteUniformMeshOrderH2Constant : Real :=
  0

/-- The concrete mesh size tends to zero in the chosen real-filter mode. -/
theorem concrete_uniform_mesh_size_tends_to_zero_v0 :
    MeshSizeTendsToZeroFilter concreteUniformMeshSize := by
  simpa [MeshSizeTendsToZeroFilter, concreteUniformMeshSize] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))

/-- The concrete mesh size is pointwise nonnegative. -/
theorem concrete_uniform_mesh_size_nonnegative_v0 :
    ∀ n : Nat, 0 ≤ concreteUniformMeshSize n := by
  intro n
  exact
    inv_nonneg.mpr
      (add_nonneg (Nat.cast_nonneg n) zero_le_one)

/-- The concrete refinement family and concrete mesh size are definitionally aligned. -/
theorem concrete_uniform_refinement_family_matches_mesh_v0 :
    concreteUniformMeshRefinementFamily = concreteUniformMeshSize := by
  rfl

/-- The zero stencil-error sequence has an eventual order-h^2 bound. -/
theorem concrete_uniform_mesh_zero_error_order_h2_bound_v0 :
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      concreteUniformMeshStencilError
      concreteUniformMeshOrderH2Constant := by
  filter_upwards with n
  simp [concreteUniformMeshStencilError, concreteUniformMeshOrderH2Constant]

/-- The zero stencil-error sequence tends to zero. -/
theorem concrete_uniform_mesh_zero_error_tends_to_zero_v0 :
    StencilErrorTendsToZeroFilter concreteUniformMeshStencilError := by
  change Tendsto (fun _n : Nat => (0 : Real)) atTop (𝓝 0)
  exact tendsto_const_nhds

/--
Semantic and analytic fields still needed to make the concrete mesh/error
normal form part of the full graph-Laplacian channel.

The mesh and zero-error estimates are no longer abstract here; the retained
fields are the continuum and graph-channel semantics that identify this
normal form with the actual refinement route.
-/
structure ConcreteUniformMeshSemanticData where
  global_smoothness_class : Prop
  global_smoothness_class_supplied : global_smoothness_class
  differentiability_order : Nat
  differentiability_order_at_least_four : 4 ≤ differentiability_order
  uniform_fourth_derivative_or_remainder_bound : Prop
  uniform_fourth_derivative_or_remainder_bound_supplied :
    uniform_fourth_derivative_or_remainder_bound
  fourth_derivative_bound : Real
  fourth_derivative_bound_nonnegative : 0 ≤ fourth_derivative_bound
  local_interval_model : Prop
  local_interval_model_supplied : local_interval_model
  taylor_remainder_theorem : Prop
  taylor_remainder_theorem_supplied : taylor_remainder_theorem
  continuum_second_derivative_semantics : Prop
  continuum_second_derivative_semantics_supplied :
    continuum_second_derivative_semantics
  continuum_laplacian_semantics : Prop
  continuum_laplacian_semantics_supplied :
    continuum_laplacian_semantics
  sample_reconstruction_compatibility : Prop
  sample_reconstruction_compatibility_supplied :
    sample_reconstruction_compatibility
  operator_domain_closure : Prop
  operator_domain_closure_supplied : operator_domain_closure
  graph_laplacian_channel_relation : Prop
  graph_laplacian_channel_relation_supplied :
    graph_laplacian_channel_relation

/--
Build the A1A10 contract using the concrete mesh and zero-error normal form.
The remaining fields are exactly the supplied semantic data above.
-/
def uniformMeshConvergenceContractOfConcreteUniformMesh
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshConvergenceContract where
  endpoint_package_subbranch_closed := True
  endpoint_package_subbranch_closed_supplied := True.intro
  two_sided_endpoint_package_available := True
  two_sided_endpoint_package_available_supplied := True.intro
  local_stencil_error_bound_route :=
    OrderH2StencilErrorBound
      concreteUniformMeshSize
      concreteUniformMeshStencilError
      concreteUniformMeshOrderH2Constant
  local_stencil_error_bound_route_supplied :=
    concrete_uniform_mesh_zero_error_order_h2_bound_v0
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
    StencilErrorTendsToZeroFilter concreteUniformMeshStencilError
  uniform_stencil_error_bound_supplied :=
    concrete_uniform_mesh_zero_error_tends_to_zero_v0
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

/-- The concrete contract exposes the concrete mesh size. -/
theorem concrete_uniform_mesh_contract_mesh_size_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceContractOfConcreteUniformMesh data).mesh_size =
      concreteUniformMeshSize := by
  rfl

/-- The concrete contract exposes the concrete refinement family. -/
theorem concrete_uniform_mesh_contract_refinement_family_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceContractOfConcreteUniformMesh data).refinement_family =
      concreteUniformMeshRefinementFamily := by
  rfl

/-- Build the A1A12 mode for the concrete mesh/zero-error normal form. -/
def concreteUniformMeshOrderH2LimitMode
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshOrderH2LimitMode
      (uniformMeshConvergenceContractOfConcreteUniformMesh data) where
  stencil_error := concreteUniformMeshStencilError
  constant := concreteUniformMeshOrderH2Constant
  constant_nonnegative := by
    simp [concreteUniformMeshOrderH2Constant]
  mesh_size_tends_to_zero_filter :=
    concrete_uniform_mesh_size_tends_to_zero_v0
  order_h_squared_error_bound_filter :=
    concrete_uniform_mesh_zero_error_order_h2_bound_v0
  refinement_independent_constant := True
  refinement_independent_constant_supplied := True.intro

/--
The concrete mesh/zero-error normal form constructs the A1A11 evidence object
through the already-proved A1A12 bridge.
-/
def uniformMeshConvergenceEvidenceOfConcreteUniformMesh
    (data : ConcreteUniformMeshSemanticData) :
    UniformMeshConvergenceEvidence
      (uniformMeshConvergenceContractOfConcreteUniformMesh data) :=
  uniformMeshConvergenceEvidenceOfOrderH2LimitMode
    (concreteUniformMeshOrderH2LimitMode data)

/-- The concrete evidence has the concrete order-h^2 bound field. -/
theorem concrete_uniform_mesh_evidence_order_h2_bound_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceEvidenceOfConcreteUniformMesh data).order_h_squared_error_bound =
      OrderH2StencilErrorBound
        concreteUniformMeshSize
        concreteUniformMeshStencilError
        concreteUniformMeshOrderH2Constant := by
  rfl

/-- The concrete evidence derives the zero-error convergence field. -/
theorem concrete_uniform_mesh_evidence_derives_stencil_error_limit_v0
    (data : ConcreteUniformMeshSemanticData) :
    (uniformMeshConvergenceEvidenceOfConcreteUniformMesh data).stencil_error_tends_to_zero := by
  exact
    uniform_mesh_evidence_derives_stencil_error_limit
      (uniformMeshConvergenceEvidenceOfConcreteUniformMesh data)

/-- Remaining objects after the concrete mesh/zero-error instantiation. -/
inductive ConcreteUniformMeshInstantiationObstruction where
  | noEndpointPackageToConcreteZeroErrorJustification
  | noNonzeroOrActualStencilErrorSequenceFromGraphData
  | noConcreteGraphChannelRelationDerivation
  | noSampleReconstructionCompatibilityDerivation
  | noContinuumLaplacianSemanticsDerivation
  | noOperatorDomainClosureDerivation
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A1A13 obstruction inventory. -/
def concreteUniformMeshInstantiationObstructionId :
    ConcreteUniformMeshInstantiationObstruction -> String
  | .noEndpointPackageToConcreteZeroErrorJustification =>
      "A2A15A1A13_OBSTRUCTION_NO_ENDPOINT_PACKAGE_TO_CONCRETE_ZERO_ERROR"
  | .noNonzeroOrActualStencilErrorSequenceFromGraphData =>
      "A2A15A1A13_OBSTRUCTION_NO_ACTUAL_STENCIL_ERROR_SEQUENCE_FROM_GRAPH_DATA"
  | .noConcreteGraphChannelRelationDerivation =>
      "A2A15A1A13_OBSTRUCTION_NO_CONCRETE_GRAPH_CHANNEL_RELATION_DERIVATION"
  | .noSampleReconstructionCompatibilityDerivation =>
      "A2A15A1A13_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY_DERIVATION"
  | .noContinuumLaplacianSemanticsDerivation =>
      "A2A15A1A13_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS_DERIVATION"
  | .noOperatorDomainClosureDerivation =>
      "A2A15A1A13_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_DERIVATION"
  | .noFullA1AChannelClosure =>
      "A2A15A1A13_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction list after the A1A13 concrete mesh normal form. -/
def concreteUniformMeshInstantiationObstructionsV0 :
    List ConcreteUniformMeshInstantiationObstruction :=
  [ .noEndpointPackageToConcreteZeroErrorJustification
  , .noNonzeroOrActualStencilErrorSequenceFromGraphData
  , .noConcreteGraphChannelRelationDerivation
  , .noSampleReconstructionCompatibilityDerivation
  , .noContinuumLaplacianSemanticsDerivation
  , .noOperatorDomainClosureDerivation
  , .noFullA1AChannelClosure
  ]

/-- The A1A13 obstruction list is stable and explicit. -/
theorem concrete_uniform_mesh_instantiation_obstructions_v0_expected :
    concreteUniformMeshInstantiationObstructionsV0 =
      [ .noEndpointPackageToConcreteZeroErrorJustification
      , .noNonzeroOrActualStencilErrorSequenceFromGraphData
      , .noConcreteGraphChannelRelationDerivation
      , .noSampleReconstructionCompatibilityDerivation
      , .noContinuumLaplacianSemanticsDerivation
      , .noOperatorDomainClosureDerivation
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor records concrete obstruction after a proof-backed mesh slice. -/
def concreteUniformMeshInstantiationSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The successor proves a bounded channel component and records obstruction. -/
theorem concrete_uniform_mesh_instantiation_successor_kinds_v0_expected :
    concreteUniformMeshInstantiationSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A13 concrete uniform mesh instantiation attempt. -/
structure ConcreteUniformMeshInstantiationStatus where
  concrete_mesh_family_defined : Prop
  concrete_mesh_family_defined_supplied :
    concrete_mesh_family_defined
  mesh_to_zero_proved : Prop
  mesh_to_zero_proved_supplied : mesh_to_zero_proved
  concrete_stencil_error_defined : Prop
  concrete_stencil_error_defined_supplied :
    concrete_stencil_error_defined
  order_h2_error_bound_proved : Prop
  order_h2_error_bound_proved_supplied :
    order_h2_error_bound_proved
  a1a12_mode_constructed : Prop
  a1a12_mode_constructed_supplied :
    a1a12_mode_constructed
  a1a11_evidence_constructed : Prop
  a1a11_evidence_constructed_supplied :
    a1a11_evidence_constructed
  graph_channel_relation_derived_from_concrete_data : Prop
  graph_channel_relation_not_derived :
    Not graph_channel_relation_derived_from_concrete_data
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  prior_a1a12_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current A1A13 status: concrete mesh and zero-error mode are theorem-backed,
while graph-channel semantic derivation remains retained.
-/
def concreteUniformMeshInstantiationStatusV0 :
    ConcreteUniformMeshInstantiationStatus where
  concrete_mesh_family_defined := True
  concrete_mesh_family_defined_supplied := True.intro
  mesh_to_zero_proved := True
  mesh_to_zero_proved_supplied := True.intro
  concrete_stencil_error_defined := True
  concrete_stencil_error_defined_supplied := True.intro
  order_h2_error_bound_proved := True
  order_h2_error_bound_proved_supplied := True.intro
  a1a12_mode_constructed := True
  a1a12_mode_constructed_supplied := True.intro
  a1a11_evidence_constructed := True
  a1a11_evidence_constructed_supplied := True.intro
  graph_channel_relation_derived_from_concrete_data := False
  graph_channel_relation_not_derived := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  prior_a1a12_retained_blocker_id :=
    phase1Blocker003A2A15A1A12ConcreteUniformMeshEvidenceRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A13ConcreteUniformMeshInstantiationRetainedId
  outcome_id := graphLaplacianConcreteUniformMeshInstantiationOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := concreteUniformMeshInstantiationSuccessorKindsV0
  obstruction_ids :=
    concreteUniformMeshInstantiationObstructionsV0.map
      concreteUniformMeshInstantiationObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def concreteUniformMeshInstantiationStatusReadoutV0 :
    ConcreteUniformMeshInstantiationStatus :=
  concreteUniformMeshInstantiationStatusV0

/-- The concrete mesh family is recorded. -/
theorem concrete_uniform_mesh_family_defined_v0 :
    ConcreteUniformMeshInstantiationStatus.concrete_mesh_family_defined
      concreteUniformMeshInstantiationStatusReadoutV0 := by
  exact
    ConcreteUniformMeshInstantiationStatus.concrete_mesh_family_defined_supplied
      concreteUniformMeshInstantiationStatusReadoutV0

/-- Mesh-to-zero is recorded as proved. -/
theorem concrete_uniform_mesh_to_zero_proved_v0 :
    ConcreteUniformMeshInstantiationStatus.mesh_to_zero_proved
      concreteUniformMeshInstantiationStatusReadoutV0 := by
  exact
    ConcreteUniformMeshInstantiationStatus.mesh_to_zero_proved_supplied
      concreteUniformMeshInstantiationStatusReadoutV0

/-- The order-h^2 zero-error bound is recorded as proved. -/
theorem concrete_uniform_mesh_order_h2_bound_proved_v0 :
    ConcreteUniformMeshInstantiationStatus.order_h2_error_bound_proved
      concreteUniformMeshInstantiationStatusReadoutV0 := by
  exact
    ConcreteUniformMeshInstantiationStatus.order_h2_error_bound_proved_supplied
      concreteUniformMeshInstantiationStatusReadoutV0

/-- The A1A12 mode construction is recorded. -/
theorem concrete_uniform_mesh_a1a12_mode_constructed_v0 :
    ConcreteUniformMeshInstantiationStatus.a1a12_mode_constructed
      concreteUniformMeshInstantiationStatusReadoutV0 := by
  exact
    ConcreteUniformMeshInstantiationStatus.a1a12_mode_constructed_supplied
      concreteUniformMeshInstantiationStatusReadoutV0

/-- The A1A11 evidence construction is recorded. -/
theorem concrete_uniform_mesh_a1a11_evidence_constructed_v0 :
    ConcreteUniformMeshInstantiationStatus.a1a11_evidence_constructed
      concreteUniformMeshInstantiationStatusReadoutV0 := by
  exact
    ConcreteUniformMeshInstantiationStatus.a1a11_evidence_constructed_supplied
      concreteUniformMeshInstantiationStatusReadoutV0

/-- Graph-channel derivation from concrete graph data remains retained. -/
theorem concrete_uniform_mesh_graph_channel_not_derived_v0 :
    Not
      (ConcreteUniformMeshInstantiationStatus.graph_channel_relation_derived_from_concrete_data
        concreteUniformMeshInstantiationStatusReadoutV0) := by
  exact
    ConcreteUniformMeshInstantiationStatus.graph_channel_relation_not_derived
      concreteUniformMeshInstantiationStatusReadoutV0

/-- A1A is not closed by the A1A13 concrete mesh normal form. -/
theorem concrete_uniform_mesh_full_a1a_not_closed_v0 :
    Not
      (ConcreteUniformMeshInstantiationStatus.full_a1a_channel_closed
        concreteUniformMeshInstantiationStatusReadoutV0) := by
  exact
    ConcreteUniformMeshInstantiationStatus.full_a1a_channel_not_closed
      concreteUniformMeshInstantiationStatusReadoutV0

/-- The prior A1A12 retained blocker id remains exposed. -/
theorem concrete_uniform_mesh_prior_a1a12_retained_id_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.prior_a1a12_retained_blocker_id =
      phase1Blocker003A2A15A1A12ConcreteUniformMeshEvidenceRetainedId := by
  rfl

/-- The A1A13 retained blocker id is exposed. -/
theorem concrete_uniform_mesh_retained_id_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A13ConcreteUniformMeshInstantiationRetainedId := by
  rfl

/-- The A1A13 outcome id is exposed. -/
theorem concrete_uniform_mesh_outcome_id_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.outcome_id =
      graphLaplacianConcreteUniformMeshInstantiationOutcomeId := by
  rfl

/-- The successor remains governed by the post-capstone anti-loop rule. -/
theorem concrete_uniform_mesh_anti_loop_rule_id_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind records bounded proof progress plus retained obstruction. -/
theorem concrete_uniform_mesh_successor_kinds_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.successor_kinds =
      concreteUniformMeshInstantiationSuccessorKindsV0 := by
  rfl

/-- The retained A1A13 obstruction ids are exposed. -/
theorem concrete_uniform_mesh_obstruction_ids_v0 :
    concreteUniformMeshInstantiationStatusReadoutV0.obstruction_ids =
      concreteUniformMeshInstantiationObstructionsV0.map
        concreteUniformMeshInstantiationObstructionId := by
  rfl

/-- Phase 2 remains unauthorized after the A1A13 instantiation attempt. -/
theorem concrete_uniform_mesh_phase2_not_authorized_v0 :
    Not concreteUniformMeshInstantiationStatusReadoutV0.phase2Authorized := by
  exact concreteUniformMeshInstantiationStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
end QFT
end ToeFormal
