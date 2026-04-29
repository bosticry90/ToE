/-
ToeFormal/QFT/ContinuumSpatialGraphLaplianSmoothTaylorRefinementConvergence.lean

General smooth Taylor/refinement convergence surface for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- define the C4-style smoothness and bounded-fourth-derivative evidence shape
- define the refinement-family, mesh-scale, Taylor-remainder, and uniform
  stencil-error convergence requirements
- prove only conditional wiring: if that evidence is supplied, it constructs
  the A1A graph-Laplacian-to-continuum-Laplacian channel evidence
- retain the actual general smooth Taylor/refinement theorem
- keep full A1A closure, Phase 2 authorization, continuum closure, seam
  closure, empirical validation, and master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianPolynomialTestClassCapstone

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianSmoothTaylorRefinementConvergence

open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianPolynomialTestClassCapstone

set_option autoImplicit false

noncomputable section

/-- Retained blocker for the general smooth Taylor/refinement theorem. -/
def phase1Blocker003A2A15A1A6SmoothTaylorRefinementRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A6_GENERAL_SMOOTH_TAYLOR_" ++
    "REFINEMENT_CONVERGENCE_RETAINED"

/-- Outcome id for the general smooth Taylor/refinement retained surface. -/
def graphLaplacianSmoothTaylorRefinementConvergenceOutcomeId :
    String :=
  "A2A15A1A6_GENERAL_SMOOTH_TAYLOR_REFINEMENT_CONVERGENCE_" ++
    "SURFACE_RECORDED_RETAINED"

/--
General smooth/refinement scheme needed to promote local stencil consistency
to uniform graph-Laplacian action convergence.
-/
structure SmoothTaylorRefinementScheme where
  smoothness_class : Prop
  smoothness_class_supplied : smoothness_class
  differentiability_order : Nat
  differentiability_order_at_least_four : 4 ≤ differentiability_order
  bounded_fourth_derivative_class : Prop
  bounded_fourth_derivative_class_supplied :
    bounded_fourth_derivative_class
  fourth_derivative_bound : Real
  fourth_derivative_bound_nonnegative : 0 ≤ fourth_derivative_bound
  refinement_family : Nat -> Real
  mesh_scale : Nat -> Real
  mesh_scale_matches_refinement_spacing : Prop
  mesh_scale_matches_refinement_spacing_supplied :
    mesh_scale_matches_refinement_spacing
  mesh_scale_nonnegative : Prop
  mesh_scale_nonnegative_supplied : mesh_scale_nonnegative
  uniform_mesh_scale_condition : Prop
  uniform_mesh_scale_condition_supplied :
    uniform_mesh_scale_condition
  mesh_tends_to_zero : Prop
  mesh_tends_to_zero_supplied : mesh_tends_to_zero
  local_interval_model : Prop
  local_interval_model_supplied : local_interval_model
  taylor_remainder_theorem : Prop
  taylor_remainder_theorem_supplied : taylor_remainder_theorem
  uniform_stencil_error_convergence : Prop
  uniform_stencil_error_convergence_supplied :
    uniform_stencil_error_convergence
  continuum_second_derivative_semantics : Prop
  continuum_second_derivative_semantics_supplied :
    continuum_second_derivative_semantics
  continuum_laplacian_semantics : Prop
  continuum_laplacian_semantics_supplied :
    continuum_laplacian_semantics
  sample_reconstruction_compatibility : Prop
  sample_reconstruction_compatibility_supplied :
    sample_reconstruction_compatibility
  operator_domain_assumptions : Prop
  operator_domain_assumptions_supplied :
    operator_domain_assumptions

/--
Evidence that a supplied smooth Taylor/refinement scheme connects to the A1A
graph-Laplacian channel contract.
-/
structure SmoothTaylorRefinementA1AEvidence
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target) where
  scheme : SmoothTaylorRefinementScheme
  graph_laplacian_scaling_convention : Prop
  graph_laplacian_scaling_convention_supplied :
    graph_laplacian_scaling_convention
  operator_action_convergence_mode : Prop
  operator_action_convergence_mode_supplied :
    operator_action_convergence_mode
  semantics_supply_parent_derivative_laplacian :
    scheme.continuum_second_derivative_semantics ->
    scheme.continuum_laplacian_semantics ->
      target.continuum_derivative_laplacian_semantics
  smooth_refinement_supplies_parent_contract_field :
    scheme.continuum_second_derivative_semantics ->
    scheme.continuum_laplacian_semantics ->
    graph_laplacian_scaling_convention ->
    scheme.uniform_mesh_scale_condition ->
    scheme.sample_reconstruction_compatibility ->
    scheme.operator_domain_assumptions ->
    scheme.uniform_stencil_error_convergence ->
    operator_action_convergence_mode ->
      contract.graph_laplacian_action_to_continuum_laplacian

/--
Supplied smooth Taylor/refinement evidence constructs the existing A1A
graph-channel evidence package.
-/
def graphChannelEvidenceOfSmoothTaylorRefinement
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      SmoothTaylorRefinementA1AEvidence target contract) :
    GraphLaplacianToContinuumLaplacianChannelEvidence
      target contract where
  continuum_second_derivative_semantics :=
    evidence.scheme.continuum_second_derivative_semantics
  continuum_second_derivative_semantics_supplied :=
    evidence.scheme.continuum_second_derivative_semantics_supplied
  continuum_laplacian_semantics :=
    evidence.scheme.continuum_laplacian_semantics
  continuum_laplacian_semantics_supplied :=
    evidence.scheme.continuum_laplacian_semantics_supplied
  graph_laplacian_scaling_convention :=
    evidence.graph_laplacian_scaling_convention
  graph_laplacian_scaling_convention_supplied :=
    evidence.graph_laplacian_scaling_convention_supplied
  refinement_relation := evidence.scheme.uniform_mesh_scale_condition
  refinement_relation_supplied :=
    evidence.scheme.uniform_mesh_scale_condition_supplied
  sample_reconstruction_compatibility :=
    evidence.scheme.sample_reconstruction_compatibility
  sample_reconstruction_compatibility_supplied :=
    evidence.scheme.sample_reconstruction_compatibility_supplied
  operator_domain_assumptions :=
    evidence.scheme.operator_domain_assumptions
  operator_domain_assumptions_supplied :=
    evidence.scheme.operator_domain_assumptions_supplied
  graph_laplacian_consistency_theorem :=
    evidence.scheme.uniform_stencil_error_convergence
  graph_laplacian_consistency_theorem_supplied :=
    evidence.scheme.uniform_stencil_error_convergence_supplied
  operator_action_convergence_mode :=
    evidence.operator_action_convergence_mode
  operator_action_convergence_mode_supplied :=
    evidence.operator_action_convergence_mode_supplied
  semantics_supply_parent_derivative_laplacian :=
    evidence.semantics_supply_parent_derivative_laplacian
  channel_supplies_parent_contract_field :=
    evidence.smooth_refinement_supplies_parent_contract_field

/-- Supplied smooth Taylor/refinement evidence fills the parent semantics. -/
theorem smooth_taylor_refinement_supplies_parent_derivative_laplacian
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      SmoothTaylorRefinementA1AEvidence target contract) :
    target.continuum_derivative_laplacian_semantics := by
  exact graph_laplacian_channel_supplies_parent_derivative_laplacian_semantics
    (graphChannelEvidenceOfSmoothTaylorRefinement evidence)

/-- Supplied smooth Taylor/refinement evidence fills the A1A parent field. -/
theorem smooth_taylor_refinement_supplies_parent_contract_field
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      SmoothTaylorRefinementA1AEvidence target contract) :
    contract.graph_laplacian_action_to_continuum_laplacian := by
  exact graph_laplacian_channel_supplies_parent_contract_field
    (graphChannelEvidenceOfSmoothTaylorRefinement evidence)

/--
The A1A6 surface records these blockers before the smooth/refinement theorem
can close the graph-Laplacian channel.
-/
inductive SmoothTaylorRefinementConvergenceObstruction where
  | noConcreteC4FunctionSpace
  | noConcreteFourthDerivativeOperator
  | noTaylorRemainderTheorem
  | noUniformMeshRefinementLimit
  | noUniformStencilErrorConvergence
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the A1A6 obstruction list. -/
def smoothTaylorRefinementConvergenceObstructionId :
    SmoothTaylorRefinementConvergenceObstruction -> String
  | .noConcreteC4FunctionSpace =>
      "A2A15A1A6_OBSTRUCTION_NO_CONCRETE_C4_FUNCTION_SPACE"
  | .noConcreteFourthDerivativeOperator =>
      "A2A15A1A6_OBSTRUCTION_NO_CONCRETE_FOURTH_DERIVATIVE_OPERATOR"
  | .noTaylorRemainderTheorem =>
      "A2A15A1A6_OBSTRUCTION_NO_TAYLOR_REMAINDER_THEOREM"
  | .noUniformMeshRefinementLimit =>
      "A2A15A1A6_OBSTRUCTION_NO_UNIFORM_MESH_REFINEMENT_LIMIT"
  | .noUniformStencilErrorConvergence =>
      "A2A15A1A6_OBSTRUCTION_NO_UNIFORM_STENCIL_ERROR_CONVERGENCE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A6_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A6_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A6_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A6_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the retained A1A6 theorem. -/
def smoothTaylorRefinementConvergenceObstructionsV0 :
    List SmoothTaylorRefinementConvergenceObstruction :=
  [ .noConcreteC4FunctionSpace
  , .noConcreteFourthDerivativeOperator
  , .noTaylorRemainderTheorem
  , .noUniformMeshRefinementLimit
  , .noUniformStencilErrorConvergence
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The A1A6 obstruction inventory is stable and explicit. -/
theorem smooth_taylor_refinement_obstructions_v0_expected :
    smoothTaylorRefinementConvergenceObstructionsV0 =
      [ .noConcreteC4FunctionSpace
      , .noConcreteFourthDerivativeOperator
      , .noTaylorRemainderTheorem
      , .noUniformMeshRefinementLimit
      , .noUniformStencilErrorConvergence
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording obstruction. -/
def smoothTaylorRefinementSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with conditional wiring above. -/
theorem smooth_taylor_refinement_successor_kinds_v0_expected :
    smoothTaylorRefinementSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A6 general smooth/refinement surface. -/
structure SmoothTaylorRefinementConvergenceStatus where
  smoothness_class_shape_defined : Prop
  smoothness_class_shape_defined_supplied :
    smoothness_class_shape_defined
  refinement_family_shape_defined : Prop
  refinement_family_shape_defined_supplied :
    refinement_family_shape_defined
  taylor_remainder_requirement_stated : Prop
  taylor_remainder_requirement_stated_supplied :
    taylor_remainder_requirement_stated
  uniform_stencil_error_requirement_stated : Prop
  uniform_stencil_error_requirement_stated_supplied :
    uniform_stencil_error_requirement_stated
  bridge_to_a1a_graph_channel_proved : Prop
  bridge_to_a1a_graph_channel_proved_supplied :
    bridge_to_a1a_graph_channel_proved
  general_smooth_taylor_refinement_theorem_proved : Prop
  general_smooth_taylor_refinement_theorem_not_proved :
    Not general_smooth_taylor_refinement_theorem_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_polynomial_capstone_outcome_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the smooth Taylor/refinement evidence shape and conditional
bridge to A1A are represented, but the actual analytic theorem remains
retained.
-/
def smoothTaylorRefinementConvergenceStatusV0 :
    SmoothTaylorRefinementConvergenceStatus where
  smoothness_class_shape_defined := True
  smoothness_class_shape_defined_supplied := True.intro
  refinement_family_shape_defined := True
  refinement_family_shape_defined_supplied := True.intro
  taylor_remainder_requirement_stated := True
  taylor_remainder_requirement_stated_supplied := True.intro
  uniform_stencil_error_requirement_stated := True
  uniform_stencil_error_requirement_stated_supplied := True.intro
  bridge_to_a1a_graph_channel_proved := True
  bridge_to_a1a_graph_channel_proved_supplied := True.intro
  general_smooth_taylor_refinement_theorem_proved := False
  general_smooth_taylor_refinement_theorem_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_polynomial_capstone_outcome_id :=
    graphLaplacianPolynomialTestClassCapstoneOutcomeId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A6SmoothTaylorRefinementRetainedId
  outcome_id := graphLaplacianSmoothTaylorRefinementConvergenceOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := smoothTaylorRefinementSuccessorKindsV0
  obstruction_ids :=
    smoothTaylorRefinementConvergenceObstructionsV0.map
      smoothTaylorRefinementConvergenceObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def smoothTaylorRefinementConvergenceStatusReadoutV0 :
    SmoothTaylorRefinementConvergenceStatus :=
  smoothTaylorRefinementConvergenceStatusV0

/-- The C4-style smoothness evidence shape is defined. -/
theorem smooth_taylor_refinement_smoothness_shape_defined_v0 :
    SmoothTaylorRefinementConvergenceStatus.smoothness_class_shape_defined
      smoothTaylorRefinementConvergenceStatusReadoutV0 := by
  exact
    SmoothTaylorRefinementConvergenceStatus.smoothness_class_shape_defined_supplied
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The refinement-family evidence shape is defined. -/
theorem smooth_taylor_refinement_family_shape_defined_v0 :
    SmoothTaylorRefinementConvergenceStatus.refinement_family_shape_defined
      smoothTaylorRefinementConvergenceStatusReadoutV0 := by
  exact
    SmoothTaylorRefinementConvergenceStatus.refinement_family_shape_defined_supplied
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The Taylor remainder theorem requirement is stated. -/
theorem smooth_taylor_refinement_taylor_requirement_stated_v0 :
    SmoothTaylorRefinementConvergenceStatus.taylor_remainder_requirement_stated
      smoothTaylorRefinementConvergenceStatusReadoutV0 := by
  exact
    SmoothTaylorRefinementConvergenceStatus.taylor_remainder_requirement_stated_supplied
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The uniform stencil-error convergence requirement is stated. -/
theorem smooth_taylor_refinement_uniform_error_requirement_stated_v0 :
    SmoothTaylorRefinementConvergenceStatus.uniform_stencil_error_requirement_stated
      smoothTaylorRefinementConvergenceStatusReadoutV0 := by
  exact
    SmoothTaylorRefinementConvergenceStatus.uniform_stencil_error_requirement_stated_supplied
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The conditional bridge to the A1A graph channel is recorded as proved. -/
theorem smooth_taylor_refinement_bridge_to_a1a_proved_v0 :
    SmoothTaylorRefinementConvergenceStatus.bridge_to_a1a_graph_channel_proved
      smoothTaylorRefinementConvergenceStatusReadoutV0 := by
  exact
    SmoothTaylorRefinementConvergenceStatus.bridge_to_a1a_graph_channel_proved_supplied
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The actual general smooth/refinement theorem remains retained. -/
theorem smooth_taylor_refinement_theorem_not_proved_v0 :
    Not (SmoothTaylorRefinementConvergenceStatus.general_smooth_taylor_refinement_theorem_proved
      smoothTaylorRefinementConvergenceStatusReadoutV0) := by
  exact
    SmoothTaylorRefinementConvergenceStatus.general_smooth_taylor_refinement_theorem_not_proved
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The A1A6 surface does not close full A1A. -/
theorem smooth_taylor_refinement_full_a1a_not_closed_v0 :
    Not (SmoothTaylorRefinementConvergenceStatus.full_a1a_channel_closed
      smoothTaylorRefinementConvergenceStatusReadoutV0) := by
  exact
    SmoothTaylorRefinementConvergenceStatus.full_a1a_channel_not_closed
      smoothTaylorRefinementConvergenceStatusReadoutV0

/-- The parent A1A retained blocker remains exposed. -/
theorem smooth_taylor_refinement_parent_retained_id_v0 :
    SmoothTaylorRefinementConvergenceStatus.parent_channel_retained_blocker_id
        smoothTaylorRefinementConvergenceStatusReadoutV0 =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior polynomial capstone outcome remains exposed. -/
theorem smooth_taylor_refinement_prior_capstone_outcome_id_v0 :
    SmoothTaylorRefinementConvergenceStatus.prior_polynomial_capstone_outcome_id
        smoothTaylorRefinementConvergenceStatusReadoutV0 =
      graphLaplacianPolynomialTestClassCapstoneOutcomeId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem smooth_taylor_refinement_retained_id_v0 :
    smoothTaylorRefinementConvergenceStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A6SmoothTaylorRefinementRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem smooth_taylor_refinement_outcome_id_v0 :
    smoothTaylorRefinementConvergenceStatusReadoutV0.outcome_id =
      graphLaplacianSmoothTaylorRefinementConvergenceOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem smooth_taylor_refinement_anti_loop_rule_id_v0 :
    smoothTaylorRefinementConvergenceStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem smooth_taylor_refinement_successor_kinds_v0 :
    smoothTaylorRefinementConvergenceStatusReadoutV0.successor_kinds =
      smoothTaylorRefinementSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem smooth_taylor_refinement_phase2_not_authorized_v0 :
    Not smoothTaylorRefinementConvergenceStatusReadoutV0.phase2Authorized := by
  exact smoothTaylorRefinementConvergenceStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianSmoothTaylorRefinementConvergence
end QFT
end ToeFormal
