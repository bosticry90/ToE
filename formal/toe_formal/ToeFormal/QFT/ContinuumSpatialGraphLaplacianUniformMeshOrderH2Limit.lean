/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit.lean

Chosen real-filter limit bridge for the A1A uniform mesh route.

Scope:
- choose the concrete sequential real-filter interpretation for mesh-size and
  stencil-error convergence
- prove that an order-h^2 stencil-error estimate implies stencil error tends
  to zero when the mesh size tends to zero
- construct the prior A1A11 evidence object from that chosen convergence mode
- retain the concrete instantiation of the mode from a graph refinement family,
  endpoint-package data, sample/reconstruction semantics, and graph-channel
  relation
-/

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Ring.Real
import ToeFormal.QFT.ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit

open Filter
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open scoped Topology

set_option autoImplicit false

noncomputable section

/--
Retained blocker after the order-h^2-to-zero limit theorem: instantiate this
chosen mode from a concrete refinement family and graph stencil error sequence.
-/
def phase1Blocker003A2A15A1A12ConcreteUniformMeshEvidenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A12_CONCRETE_UNIFORM_MESH_" ++
    "EVIDENCE_RETAINED"

/-- Outcome id for the proven order-h^2 stencil-error limit bridge. -/
def graphLaplacianUniformMeshOrderH2LimitOutcomeId : String :=
  "A2A15A1A12_ORDER_H2_STENCIL_ERROR_LIMIT_PROVED_" ++
    "CONCRETE_EVIDENCE_RETAINED"

/-- The chosen mesh-size convergence mode: sequential real convergence to 0. -/
def MeshSizeTendsToZeroFilter (meshSize : Nat -> Real) : Prop :=
  Tendsto meshSize atTop (𝓝 0)

/-- The chosen stencil-error convergence mode: sequential real convergence to 0. -/
def StencilErrorTendsToZeroFilter (stencilError : Nat -> Real) : Prop :=
  Tendsto stencilError atTop (𝓝 0)

/-- A concrete order-h^2 stencil-error estimate in the chosen real-filter mode. -/
def OrderH2StencilErrorBound
    (meshSize stencilError : Nat -> Real)
    (constant : Real) : Prop :=
  ∀ᶠ n in atTop, ‖stencilError n‖ ≤ constant * (meshSize n)^2

/--
Concrete real-filter mode required to derive the A1A11 stencil-error limit.

The `constant` is a single refinement-independent real number.  The explicit
`constant_nonnegative` field records the intended analytic meaning even though
the squeeze proof below only needs the stated eventual norm bound.
-/
structure UniformMeshOrderH2LimitMode
    (contract : UniformMeshConvergenceContract) where
  stencil_error : Nat -> Real
  constant : Real
  constant_nonnegative : 0 ≤ constant
  mesh_size_tends_to_zero_filter :
    MeshSizeTendsToZeroFilter contract.mesh_size
  order_h_squared_error_bound_filter :
    OrderH2StencilErrorBound contract.mesh_size stencil_error constant
  refinement_independent_constant : Prop
  refinement_independent_constant_supplied :
    refinement_independent_constant

/--
The order-h^2 estimate implies the stencil error tends to zero in the chosen
sequential real-filter mode.
-/
theorem order_h_squared_bound_implies_stencil_error_tends_to_zero
    {contract : UniformMeshConvergenceContract}
    (mode : UniformMeshOrderH2LimitMode contract) :
    StencilErrorTendsToZeroFilter mode.stencil_error := by
  have hmesh_sq :
      Tendsto (fun n => (contract.mesh_size n)^2) atTop (𝓝 0) := by
    simpa [MeshSizeTendsToZeroFilter] using
      mode.mesh_size_tends_to_zero_filter.pow 2
  have hbound :
      Tendsto
        (fun n => mode.constant * (contract.mesh_size n)^2)
        atTop
        (𝓝 0) := by
    simpa using hmesh_sq.const_mul mode.constant
  exact
    squeeze_zero_norm'
      mode.order_h_squared_error_bound_filter
      hbound

/--
The chosen real-filter mode constructs the prior A1A11 evidence object without
supplying a separate stencil-error-to-zero axiom.
-/
def uniformMeshConvergenceEvidenceOfOrderH2LimitMode
    {contract : UniformMeshConvergenceContract}
    (mode : UniformMeshOrderH2LimitMode contract) :
    UniformMeshConvergenceEvidence contract where
  mesh_size_tends_to_zero_evidence :=
    contract.mesh_size_tends_to_zero_supplied
  uniform_fourth_derivative_bound_evidence :=
    contract.uniform_fourth_derivative_or_remainder_bound_supplied
  refinement_independent_constant :=
    mode.refinement_independent_constant
  refinement_independent_constant_supplied :=
    mode.refinement_independent_constant_supplied
  order_h_squared_error_bound :=
    OrderH2StencilErrorBound
      contract.mesh_size
      mode.stencil_error
      mode.constant
  order_h_squared_error_bound_supplied :=
    mode.order_h_squared_error_bound_filter
  stencil_error_tends_to_zero :=
    StencilErrorTendsToZeroFilter mode.stencil_error
  stencil_error_tends_to_zero_supplied :=
    order_h_squared_bound_implies_stencil_error_tends_to_zero mode
  uniform_stencil_error_bound_evidence :=
    contract.uniform_stencil_error_bound_supplied
  graph_channel_relation_evidence :=
    contract.graph_laplacian_channel_relation_supplied
  order_h_squared_bound_supplies_stencil_error_limit := by
    intro _meshToZero _fourthBound _constant _orderBound
    exact order_h_squared_bound_implies_stencil_error_tends_to_zero mode

/-- The mode-derived evidence has the chosen stencil-error limit field. -/
theorem order_h2_mode_evidence_stencil_error_limit_v0
    {contract : UniformMeshConvergenceContract}
    (mode : UniformMeshOrderH2LimitMode contract) :
    (uniformMeshConvergenceEvidenceOfOrderH2LimitMode mode).stencil_error_tends_to_zero =
      StencilErrorTendsToZeroFilter mode.stencil_error := by
  rfl

/-- The mode-derived evidence uses the concrete order-h^2 bound field. -/
theorem order_h2_mode_evidence_order_h2_bound_v0
    {contract : UniformMeshConvergenceContract}
    (mode : UniformMeshOrderH2LimitMode contract) :
    (uniformMeshConvergenceEvidenceOfOrderH2LimitMode mode).order_h_squared_error_bound =
      OrderH2StencilErrorBound
        contract.mesh_size
        mode.stencil_error
        mode.constant := by
  rfl

/-- Remaining concrete objects after the order-h^2 limit theorem. -/
inductive UniformMeshOrderH2LimitObstruction where
  | noConcreteRefinementFamily
  | noConcreteStencilErrorSequence
  | noEndpointPackageToUniformOrderH2Estimate
  | noGraphChannelRelationDerivation
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A1A12 obstruction inventory. -/
def uniformMeshOrderH2LimitObstructionId :
    UniformMeshOrderH2LimitObstruction -> String
  | .noConcreteRefinementFamily =>
      "A2A15A1A12_OBSTRUCTION_NO_CONCRETE_REFINEMENT_FAMILY"
  | .noConcreteStencilErrorSequence =>
      "A2A15A1A12_OBSTRUCTION_NO_CONCRETE_STENCIL_ERROR_SEQUENCE"
  | .noEndpointPackageToUniformOrderH2Estimate =>
      "A2A15A1A12_OBSTRUCTION_NO_ENDPOINT_PACKAGE_TO_UNIFORM_ORDER_H2_ESTIMATE"
  | .noGraphChannelRelationDerivation =>
      "A2A15A1A12_OBSTRUCTION_NO_GRAPH_CHANNEL_RELATION_DERIVATION"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A12_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A12_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A12_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A12_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction list after the A1A12 limit theorem. -/
def uniformMeshOrderH2LimitObstructionsV0 :
    List UniformMeshOrderH2LimitObstruction :=
  [ .noConcreteRefinementFamily
  , .noConcreteStencilErrorSequence
  , .noEndpointPackageToUniformOrderH2Estimate
  , .noGraphChannelRelationDerivation
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The A1A12 obstruction list is stable and explicit. -/
theorem uniform_mesh_order_h2_limit_obstructions_v0_expected :
    uniformMeshOrderH2LimitObstructionsV0 =
      [ .noConcreteRefinementFamily
      , .noConcreteStencilErrorSequence
      , .noEndpointPackageToUniformOrderH2Estimate
      , .noGraphChannelRelationDerivation
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor records concrete obstruction after the limit theorem. -/
def uniformMeshOrderH2LimitSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording. -/
theorem uniform_mesh_order_h2_limit_successor_kinds_v0_expected :
    uniformMeshOrderH2LimitSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A12 order-h^2 limit theorem. -/
structure UniformMeshOrderH2LimitStatus where
  chosen_real_filter_mode_defined : Prop
  chosen_real_filter_mode_defined_supplied :
    chosen_real_filter_mode_defined
  mesh_to_zero_mode_defined : Prop
  mesh_to_zero_mode_defined_supplied :
    mesh_to_zero_mode_defined
  order_h2_bound_mode_defined : Prop
  order_h2_bound_mode_defined_supplied :
    order_h2_bound_mode_defined
  order_h2_to_stencil_zero_theorem_proved : Prop
  order_h2_to_stencil_zero_theorem_proved_supplied :
    order_h2_to_stencil_zero_theorem_proved
  a1a11_evidence_constructor_proved : Prop
  a1a11_evidence_constructor_proved_supplied :
    a1a11_evidence_constructor_proved
  concrete_mode_instantiated_from_graph_data : Prop
  concrete_mode_instantiated_from_graph_data_not_proved :
    Not concrete_mode_instantiated_from_graph_data
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  prior_a1a11_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the order-h^2-to-zero bridge is proved for the chosen real
filter mode, but concrete graph/refinement instantiation remains retained.
-/
def uniformMeshOrderH2LimitStatusV0 :
    UniformMeshOrderH2LimitStatus where
  chosen_real_filter_mode_defined := True
  chosen_real_filter_mode_defined_supplied := True.intro
  mesh_to_zero_mode_defined := True
  mesh_to_zero_mode_defined_supplied := True.intro
  order_h2_bound_mode_defined := True
  order_h2_bound_mode_defined_supplied := True.intro
  order_h2_to_stencil_zero_theorem_proved := True
  order_h2_to_stencil_zero_theorem_proved_supplied := True.intro
  a1a11_evidence_constructor_proved := True
  a1a11_evidence_constructor_proved_supplied := True.intro
  concrete_mode_instantiated_from_graph_data := False
  concrete_mode_instantiated_from_graph_data_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  prior_a1a11_retained_blocker_id :=
    phase1Blocker003A2A15A1A11UniformMeshConvergenceEvidenceRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A12ConcreteUniformMeshEvidenceRetainedId
  outcome_id := graphLaplacianUniformMeshOrderH2LimitOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := uniformMeshOrderH2LimitSuccessorKindsV0
  obstruction_ids :=
    uniformMeshOrderH2LimitObstructionsV0.map
      uniformMeshOrderH2LimitObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def uniformMeshOrderH2LimitStatusReadoutV0 :
    UniformMeshOrderH2LimitStatus :=
  uniformMeshOrderH2LimitStatusV0

/-- The chosen real-filter convergence mode is defined. -/
theorem uniform_mesh_order_h2_chosen_mode_defined_v0 :
    UniformMeshOrderH2LimitStatus.chosen_real_filter_mode_defined
      uniformMeshOrderH2LimitStatusReadoutV0 := by
  exact
    UniformMeshOrderH2LimitStatus.chosen_real_filter_mode_defined_supplied
      uniformMeshOrderH2LimitStatusReadoutV0

/-- The mesh-to-zero real-filter mode is defined. -/
theorem uniform_mesh_order_h2_mesh_to_zero_mode_defined_v0 :
    UniformMeshOrderH2LimitStatus.mesh_to_zero_mode_defined
      uniformMeshOrderH2LimitStatusReadoutV0 := by
  exact
    UniformMeshOrderH2LimitStatus.mesh_to_zero_mode_defined_supplied
      uniformMeshOrderH2LimitStatusReadoutV0

/-- The order-h^2 bound mode is defined. -/
theorem uniform_mesh_order_h2_bound_mode_defined_v0 :
    UniformMeshOrderH2LimitStatus.order_h2_bound_mode_defined
      uniformMeshOrderH2LimitStatusReadoutV0 := by
  exact
    UniformMeshOrderH2LimitStatus.order_h2_bound_mode_defined_supplied
      uniformMeshOrderH2LimitStatusReadoutV0

/-- The order-h^2-to-stencil-zero theorem is recorded as proved. -/
theorem uniform_mesh_order_h2_to_zero_theorem_proved_v0 :
    UniformMeshOrderH2LimitStatus.order_h2_to_stencil_zero_theorem_proved
      uniformMeshOrderH2LimitStatusReadoutV0 := by
  exact
    UniformMeshOrderH2LimitStatus.order_h2_to_stencil_zero_theorem_proved_supplied
      uniformMeshOrderH2LimitStatusReadoutV0

/-- The A1A11 evidence constructor from the chosen mode is recorded. -/
theorem uniform_mesh_order_h2_a1a11_constructor_proved_v0 :
    UniformMeshOrderH2LimitStatus.a1a11_evidence_constructor_proved
      uniformMeshOrderH2LimitStatusReadoutV0 := by
  exact
    UniformMeshOrderH2LimitStatus.a1a11_evidence_constructor_proved_supplied
      uniformMeshOrderH2LimitStatusReadoutV0

/-- Concrete graph/refinement instantiation of the chosen mode remains retained. -/
theorem uniform_mesh_order_h2_concrete_mode_not_instantiated_v0 :
    Not
      (UniformMeshOrderH2LimitStatus.concrete_mode_instantiated_from_graph_data
        uniformMeshOrderH2LimitStatusReadoutV0) := by
  exact
    UniformMeshOrderH2LimitStatus.concrete_mode_instantiated_from_graph_data_not_proved
      uniformMeshOrderH2LimitStatusReadoutV0

/-- A1A is not closed by the A1A12 limit theorem. -/
theorem uniform_mesh_order_h2_full_a1a_not_closed_v0 :
    Not
      (UniformMeshOrderH2LimitStatus.full_a1a_channel_closed
        uniformMeshOrderH2LimitStatusReadoutV0) := by
  exact
    UniformMeshOrderH2LimitStatus.full_a1a_channel_not_closed
      uniformMeshOrderH2LimitStatusReadoutV0

/-- The prior A1A11 retained blocker id remains exposed. -/
theorem uniform_mesh_order_h2_prior_a1a11_retained_id_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.prior_a1a11_retained_blocker_id =
      phase1Blocker003A2A15A1A11UniformMeshConvergenceEvidenceRetainedId := by
  rfl

/-- The A1A12 retained blocker id is exposed. -/
theorem uniform_mesh_order_h2_retained_id_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A12ConcreteUniformMeshEvidenceRetainedId := by
  rfl

/-- The A1A12 outcome id is exposed. -/
theorem uniform_mesh_order_h2_outcome_id_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.outcome_id =
      graphLaplacianUniformMeshOrderH2LimitOutcomeId := by
  rfl

/-- The successor remains governed by the post-capstone anti-loop rule. -/
theorem uniform_mesh_order_h2_anti_loop_rule_id_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem uniform_mesh_order_h2_successor_kinds_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.successor_kinds =
      uniformMeshOrderH2LimitSuccessorKindsV0 := by
  rfl

/-- The retained A1A12 obstruction ids are exposed. -/
theorem uniform_mesh_order_h2_obstruction_ids_v0 :
    uniformMeshOrderH2LimitStatusReadoutV0.obstruction_ids =
      uniformMeshOrderH2LimitObstructionsV0.map
        uniformMeshOrderH2LimitObstructionId := by
  rfl

/-- Phase 2 remains unauthorized after the A1A12 limit theorem. -/
theorem uniform_mesh_order_h2_phase2_not_authorized_v0 :
    Not uniformMeshOrderH2LimitStatusReadoutV0.phase2Authorized := by
  exact uniformMeshOrderH2LimitStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
end QFT
end ToeFormal
