/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError.lean

A1A17 parent graph-channel interface-map review after A1A16 actual
graph-stencil error identification and the A1A semantic closure review.

Scope:
- isolate the actual graph-error evidence-only package from A1A16
- verify that this evidence still supplies the actual stencil-error limit
- test whether that evidence, without the supplied parent semantic map from
  the closure review, can fill an arbitrary parent graph-channel field
- record the retained answer: the parent field is an uninterpreted proposition
  in the parent contract, so the semantic map remains required
- keep A2A15A1 closure, Phase 2 authorization, and Phase 0-5 completion out
  of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianGraphChannelSemanticClosureReview

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergence
open ContinuumSpatialGraphLaplacianUniformMeshConvergenceEvidence
open ContinuumSpatialGraphLaplacianUniformMeshOrderH2Limit
open ContinuumSpatialGraphLaplacianConcreteUniformMeshInstantiation
open ContinuumSpatialGraphLaplacianEndpointPackageStencilErrorUniformBound
open ContinuumSpatialGraphLaplacianActualGraphStencilErrorIdentification
open ContinuumSpatialGraphLaplacianGraphChannelSemanticClosureReview

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A17 parent-interface-map review. -/
def a1a17ParentInterfaceMapFromActualGraphErrorSurfaceId : String :=
  "A2A15A1A17_PARENT_INTERFACE_MAP_FROM_ACTUAL_GRAPH_ERROR"

/-- Retained blocker after the parent interface map is not derived. -/
def phase1Blocker003A2A15A1A17ParentGraphChannelInterfaceMapRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A17_PARENT_GRAPH_CHANNEL_" ++
    "INTERFACE_MAP_RETAINED"

/-- Outcome id for the retained A1A17 interface-map review. -/
def parentGraphChannelInterfaceMapRetainedOutcomeId : String :=
  "PARENT_GRAPH_CHANNEL_INTERFACE_MAP_RETAINED"

/--
A1A16 actual-error evidence with the parent semantic map deliberately omitted.

This package carries the concrete semantic data and endpoint-package family
needed to construct the A1A16 actual graph-action error sequence and A1A11
evidence object.  It does not contain any field that maps those facts into an
arbitrary parent `AnalyticIntervalLiftConvergenceContract`.
-/
structure ActualGraphErrorEvidenceOnly
    {f : Real -> Real}
    (x C : Real) where
  data : ConcreteUniformMeshSemanticData
  family : EndpointPackageStencilErrorFamilyData f x C

/-- Evidence-only A1A16 data still constructs the actual A1A11 evidence. -/
def uniformMeshConvergenceEvidenceOfActualGraphErrorEvidenceOnly
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    UniformMeshConvergenceEvidence
      (uniformMeshConvergenceContractOfActualGraphStencilError
        evidenceOnly.data evidenceOnly.family) :=
  uniformMeshConvergenceEvidenceOfActualGraphStencilError
    evidenceOnly.data evidenceOnly.family

/-- Evidence-only A1A16 data still derives the actual stencil-error limit. -/
theorem actual_graph_error_evidence_only_derives_stencil_limit_v0
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    (uniformMeshConvergenceEvidenceOfActualGraphErrorEvidenceOnly
        evidenceOnly).stencil_error_tends_to_zero := by
  exact
    uniform_mesh_evidence_derives_stencil_error_limit
      (uniformMeshConvergenceEvidenceOfActualGraphErrorEvidenceOnly
        evidenceOnly)

/--
Semantic-map-free parent interface map tested by this review.

The quantified parent contract is intentionally arbitrary.  A successful value
would mean actual graph-error evidence alone fills every parent graph-channel
field, without the semantic bridge required in the previous review.
-/
def SemanticMapFreeParentGraphChannelInterfaceMap
    {f : Real -> Real}
    {x C : Real}
    (_evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) : Prop :=
  ∀ {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (parentContract : AnalyticIntervalLiftConvergenceContract target),
      parentContract.graph_laplacian_action_to_continuum_laplacian

/-- Counterexample target using the already-checked finite two-point model. -/
def parentInterfaceCounterexampleTarget :
    AnalyticIntervalLiftTarget TwoPointSpatialInterval where
  continuum_problem := twoPointSpatialBoundaryProblem
  continuum_raw_boundary_flux := twoPointRawBoundaryFlux
  continuum_problem_selected := two_point_spatial_boundary_problem_selected
  analytic_interval_domain_model := True
  continuum_derivative_laplacian_semantics := True
  boundary_trace_normal_derivative_semantics := True
  domain_regular_for_limit_passage := True
  orientation_convention_for_limit := True

/--
Counterexample parent contract whose graph-channel field is `False`.

This is legal because the parent contract currently stores the graph-channel
claim as an uninterpreted proposition.  Therefore no evidence-only package can
produce this field for all parent contracts without a semantic bridge.
-/
def parentInterfaceCounterexampleContract :
    AnalyticIntervalLiftConvergenceContract
      parentInterfaceCounterexampleTarget where
  ApproximationIndex := Unit
  sample := fun _ f => f
  reconstruct := fun _ f => f
  graph_laplacian_action_to_continuum_laplacian := False
  finite_endpoint_flux_to_continuum_boundary_flux := True
  finite_raw_ibp_to_continuum_green_identity := True
  finite_pairing_to_continuum_pairing := True
  trace_normal_derivative_convergence := True
  domain_regular_for_limit_passage := True
  orientation_convention_compatible := True
  separating_test_class_for_limit := True
  contract_implies_raw_spatial_ibp := by
    intro hGraph _finitePairing _finiteRawIBPGreen _domain
    exact False.elim hGraph
  contract_implies_boundary_flux_representation := by
    intro _finiteEndpointFlux _traceNormal _orientation
    exact two_point_boundary_flux_representation

/--
A1A16 actual graph-error evidence alone cannot supply the parent interface map
for arbitrary parent contracts.
-/
theorem actual_graph_error_evidence_only_cannot_close_parent_interface_v0
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    Not (SemanticMapFreeParentGraphChannelInterfaceMap evidenceOnly) := by
  intro hMap
  exact
    hMap
      parentInterfaceCounterexampleTarget
      parentInterfaceCounterexampleContract

/-- Remaining objects after the A1A17 parent-interface-map review. -/
inductive ParentInterfaceMapFromActualGraphErrorObstruction where
  | parentGraphChannelFieldUninterpreted
  | noSemanticMapFromActualErrorEvidence
  | noContinuumLaplacianSemanticClosure
  | noOperatorDomainClosureFromActualError
  | noParentGraphRelation
  | noA2A15A1AssemblyReview
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A17 objects. -/
def parentInterfaceMapFromActualGraphErrorObstructionId :
    ParentInterfaceMapFromActualGraphErrorObstruction -> String
  | .parentGraphChannelFieldUninterpreted =>
      "A1A17_OBSTRUCTION_PARENT_GRAPH_CHANNEL_FIELD_UNINTERPRETED"
  | .noSemanticMapFromActualErrorEvidence =>
      "A1A17_OBSTRUCTION_NO_SEMANTIC_MAP_FROM_ACTUAL_ERROR_EVIDENCE"
  | .noContinuumLaplacianSemanticClosure =>
      "A1A17_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTIC_CLOSURE"
  | .noOperatorDomainClosureFromActualError =>
      "A1A17_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE_FROM_ACTUAL_ERROR"
  | .noParentGraphRelation =>
      "A1A17_OBSTRUCTION_NO_PARENT_GRAPH_RELATION"
  | .noA2A15A1AssemblyReview =>
      "A1A17_OBSTRUCTION_NO_A2A15A1_ASSEMBLY_REVIEW"
  | .noPhase2Authorization =>
      "A1A17_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A17 interface-map review. -/
def parentInterfaceMapFromActualGraphErrorObstructionsV0 :
    List ParentInterfaceMapFromActualGraphErrorObstruction :=
  [ .parentGraphChannelFieldUninterpreted
  , .noSemanticMapFromActualErrorEvidence
  , .noContinuumLaplacianSemanticClosure
  , .noOperatorDomainClosureFromActualError
  , .noParentGraphRelation
  , .noA2A15A1AssemblyReview
  , .noPhase2Authorization
  ]

/-- The A1A17 obstruction list is stable and explicit. -/
theorem parent_interface_map_from_actual_graph_error_obstructions_v0_expected :
    parentInterfaceMapFromActualGraphErrorObstructionsV0 =
      [ .parentGraphChannelFieldUninterpreted
      , .noSemanticMapFromActualErrorEvidence
      , .noContinuumLaplacianSemanticClosure
      , .noOperatorDomainClosureFromActualError
      , .noParentGraphRelation
      , .noA2A15A1AssemblyReview
      , .noPhase2Authorization
      ] := by
  rfl

/-- This successor records the concrete obstruction to map-free closure. -/
def parentInterfaceMapFromActualGraphErrorSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The A1A17 successor kind is obstruction-recording. -/
theorem parent_interface_map_from_actual_graph_error_successor_kinds_v0_expected :
    parentInterfaceMapFromActualGraphErrorSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A17 parent-interface-map review. -/
structure ParentInterfaceMapFromActualGraphErrorStatus where
  review_surface_defined : Prop
  review_surface_defined_supplied : review_surface_defined
  actual_graph_error_evidence_only_available : Prop
  actual_graph_error_evidence_only_available_supplied :
    actual_graph_error_evidence_only_available
  actual_stencil_limit_available : Prop
  actual_stencil_limit_available_supplied :
    actual_stencil_limit_available
  semantic_map_free_counterexample_recorded : Prop
  semantic_map_free_counterexample_supplied :
    semantic_map_free_counterexample_recorded
  parent_interface_map_derived_without_semantic_map : Prop
  parent_interface_map_not_derived :
    Not parent_interface_map_derived_without_semantic_map
  prior_conditional_bridge_available : Prop
  prior_conditional_bridge_available_supplied :
    prior_conditional_bridge_available
  graph_channel_closed : Prop
  graph_channel_not_closed : Not graph_channel_closed
  a2a15a1_ready_for_review : Prop
  a2a15a1_not_ready_for_review : Not a2a15a1_ready_for_review
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  surface_id : String
  prior_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String

/--
Current A1A17 result: actual graph-error evidence is available, but without a
parent semantic map it cannot fill arbitrary parent graph-channel fields.
-/
def parentInterfaceMapFromActualGraphErrorStatusV0 :
    ParentInterfaceMapFromActualGraphErrorStatus where
  review_surface_defined := True
  review_surface_defined_supplied := True.intro
  actual_graph_error_evidence_only_available := True
  actual_graph_error_evidence_only_available_supplied := True.intro
  actual_stencil_limit_available := True
  actual_stencil_limit_available_supplied := True.intro
  semantic_map_free_counterexample_recorded := True
  semantic_map_free_counterexample_supplied := True.intro
  parent_interface_map_derived_without_semantic_map := False
  parent_interface_map_not_derived := by
    intro h
    exact h
  prior_conditional_bridge_available := True
  prior_conditional_bridge_available_supplied := True.intro
  graph_channel_closed := False
  graph_channel_not_closed := by
    intro h
    exact h
  a2a15a1_ready_for_review := False
  a2a15a1_not_ready_for_review := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := a1a17ParentInterfaceMapFromActualGraphErrorSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A16GraphChannelSemanticClosureRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A17ParentGraphChannelInterfaceMapRetainedId
  outcome_id := parentGraphChannelInterfaceMapRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := parentInterfaceMapFromActualGraphErrorSuccessorKindsV0
  obstruction_ids :=
    parentInterfaceMapFromActualGraphErrorObstructionsV0.map
      parentInterfaceMapFromActualGraphErrorObstructionId

/-- Short proof-facing status alias. -/
def parentInterfaceMapFromActualGraphErrorStatusReadoutV0 :
    ParentInterfaceMapFromActualGraphErrorStatus :=
  parentInterfaceMapFromActualGraphErrorStatusV0

/-- The A1A17 review surface is recorded. -/
theorem parent_interface_map_review_surface_defined_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.review_surface_defined := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.review_surface_defined_supplied

/-- A1A16 evidence-only data is available to the review. -/
theorem parent_interface_map_actual_error_evidence_only_available_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.actual_graph_error_evidence_only_available := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.actual_graph_error_evidence_only_available_supplied

/-- The actual stencil-limit evidence remains available. -/
theorem parent_interface_map_actual_stencil_limit_available_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.actual_stencil_limit_available := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.actual_stencil_limit_available_supplied

/-- The semantic-map-free counterexample is recorded. -/
theorem parent_interface_map_counterexample_recorded_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.semantic_map_free_counterexample_recorded := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.semantic_map_free_counterexample_supplied

/-- The parent interface map is not derived without a semantic map. -/
theorem parent_interface_map_without_semantic_map_not_derived_v0 :
    Not
      (parentInterfaceMapFromActualGraphErrorStatusReadoutV0
        |>.parent_interface_map_derived_without_semantic_map) := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.parent_interface_map_not_derived

/-- The prior conditional bridge remains available but conditional. -/
theorem parent_interface_map_prior_conditional_bridge_available_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.prior_conditional_bridge_available := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.prior_conditional_bridge_available_supplied

/-- The graph channel is not closed by the A1A17 review. -/
theorem parent_interface_map_graph_channel_not_closed_v0 :
    Not
      (parentInterfaceMapFromActualGraphErrorStatusReadoutV0
        |>.graph_channel_closed) := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.graph_channel_not_closed

/-- A2A15A1 remains not ready for review after A1A17. -/
theorem parent_interface_map_a2a15a1_not_ready_v0 :
    Not
      (parentInterfaceMapFromActualGraphErrorStatusReadoutV0
        |>.a2a15a1_ready_for_review) := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.a2a15a1_not_ready_for_review

/-- Phase 2 remains unauthorized after A1A17. -/
theorem parent_interface_map_phase2_not_authorized_v0 :
    Not
      (parentInterfaceMapFromActualGraphErrorStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A17 retained blocker id is exposed. -/
theorem parent_interface_map_retained_id_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A17ParentGraphChannelInterfaceMapRetainedId := by
  rfl

/-- The A1A17 outcome id is exposed. -/
theorem parent_interface_map_outcome_id_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0.outcome_id =
      parentGraphChannelInterfaceMapRetainedOutcomeId := by
  rfl

/-- The A1A17 obstruction ids are exposed. -/
theorem parent_interface_map_obstruction_ids_v0 :
    parentInterfaceMapFromActualGraphErrorStatusReadoutV0.obstruction_ids =
      parentInterfaceMapFromActualGraphErrorObstructionsV0.map
        parentInterfaceMapFromActualGraphErrorObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
end QFT
end ToeFormal
