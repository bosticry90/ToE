/-
ToeFormal/QFT/ContinuumSpatialAnalyticIntervalLift.lean

Retained A2A15A1 analytic interval lift contract.

Scope:
- state the finite-to-continuum lift required after the two-endpoint raw
  spatial IBP proof contract
- name the convergence channels from the finite graph-Laplacian surrogate to
  continuum derivative/Laplacian semantics, boundary flux, and Green identity
- prove that supplied lift evidence would feed the existing A2A15/A2A14 route
- keep analytic convergence proof, continuum Laplacian construction, nonzero
  normal-derivative flux, Phase 2 authorization, seam closure, empirical
  validation, and master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialRawIBPProofContract

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialAnalyticIntervalLift

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumNonzeroScalarKineticOperatorDomainClosure
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialLaplacianBoundaryFluxSubblockers
open ContinuumSpatialRawIBPProofContract

set_option autoImplicit false

noncomputable section

/-- Retained blocker after stating the A2A15A1 analytic interval lift. -/
def phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1_ANALYTIC_INTERVAL_LIFT_RETAINED"

/-- Outcome id for the retained analytic interval lift contract. -/
def analyticIntervalLiftContractOutcomeId : String :=
  "A2A15A1_ANALYTIC_INTERVAL_LIFT_CONTRACT_RECORDED_RETAINED"

/-- Remaining objects after the A2A15A1 contract is stated. -/
inductive Phase1Blocker003A2A15A1MissingObject where
  | analyticIntervalDomainModel
  | continuumDerivativeLaplacianSemantics
  | finiteToContinuumApproximationScheme
  | graphLaplacianActionConvergence
  | finiteEndpointFluxConvergence
  | finiteRawIBPToGreenIdentityConvergence
  | finitePairingConvergence
  | traceNormalDerivativeConvergence
  | domainRegularityForLimitPassage
  | orientationConventionForLimit
  | separatingTestClassForLimit
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A2A15A1 objects. -/
def phase1Blocker003A2A15A1MissingObjectId :
    Phase1Blocker003A2A15A1MissingObject -> String
  | .analyticIntervalDomainModel =>
      "003A2A15A1_ANALYTIC_INTERVAL_DOMAIN_MODEL_RETAINED"
  | .continuumDerivativeLaplacianSemantics =>
      "003A2A15A1_CONTINUUM_DERIVATIVE_LAPLACIAN_SEMANTICS_RETAINED"
  | .finiteToContinuumApproximationScheme =>
      "003A2A15A1_FINITE_TO_CONTINUUM_APPROXIMATION_SCHEME_RETAINED"
  | .graphLaplacianActionConvergence =>
      "003A2A15A1_GRAPH_LAPLACIAN_ACTION_CONVERGENCE_RETAINED"
  | .finiteEndpointFluxConvergence =>
      "003A2A15A1_FINITE_ENDPOINT_FLUX_CONVERGENCE_RETAINED"
  | .finiteRawIBPToGreenIdentityConvergence =>
      "003A2A15A1_FINITE_RAW_IBP_GREEN_IDENTITY_CONVERGENCE_RETAINED"
  | .finitePairingConvergence =>
      "003A2A15A1_FINITE_PAIRING_CONVERGENCE_RETAINED"
  | .traceNormalDerivativeConvergence =>
      "003A2A15A1_TRACE_NORMAL_DERIVATIVE_CONVERGENCE_RETAINED"
  | .domainRegularityForLimitPassage =>
      "003A2A15A1_DOMAIN_REGULARITY_FOR_LIMIT_PASSAGE_RETAINED"
  | .orientationConventionForLimit =>
      "003A2A15A1_ORIENTATION_CONVENTION_FOR_LIMIT_RETAINED"
  | .separatingTestClassForLimit =>
      "003A2A15A1_SEPARATING_TEST_CLASS_FOR_LIMIT_RETAINED"

/-- The retained A2A15A1 object list is stable and explicit. -/
def phase1Blocker003A2A15A1MissingObjectsV0 :
    List Phase1Blocker003A2A15A1MissingObject :=
  [ .analyticIntervalDomainModel
  , .continuumDerivativeLaplacianSemantics
  , .finiteToContinuumApproximationScheme
  , .graphLaplacianActionConvergence
  , .finiteEndpointFluxConvergence
  , .finiteRawIBPToGreenIdentityConvergence
  , .finitePairingConvergence
  , .traceNormalDerivativeConvergence
  , .domainRegularityForLimitPassage
  , .orientationConventionForLimit
  , .separatingTestClassForLimit
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a15a1_missing_objects_v0_expected :
    phase1Blocker003A2A15A1MissingObjectsV0 =
      [ .analyticIntervalDomainModel
      , .continuumDerivativeLaplacianSemantics
      , .finiteToContinuumApproximationScheme
      , .graphLaplacianActionConvergence
      , .finiteEndpointFluxConvergence
      , .finiteRawIBPToGreenIdentityConvergence
      , .finitePairingConvergence
      , .traceNormalDerivativeConvergence
      , .domainRegularityForLimitPassage
      , .orientationConventionForLimit
      , .separatingTestClassForLimit
      ] := by
  rfl

/--
Continuum target for lifting the checked two-endpoint raw-IBP theorem to an
analytic interval model.
-/
structure AnalyticIntervalLiftTarget (ContinuumPoint : Type) where
  continuum_problem : ScalarKineticBoundaryProblem ContinuumPoint
  continuum_raw_boundary_flux : RawSpatialBoundaryFlux ContinuumPoint
  continuum_problem_selected :
    ScalarKineticBoundaryProblemSelected continuum_problem
  analytic_interval_domain_model : Prop
  continuum_derivative_laplacian_semantics : Prop
  boundary_trace_normal_derivative_semantics : Prop
  domain_regular_for_limit_passage : Prop
  orientation_convention_for_limit : Prop

/--
Finite-to-continuum convergence contract for the A2A15A analytic interval lift.

The contract explicitly names the three required convergence channels:
graph-Laplacian action to continuum Laplacian, finite endpoint flux to
continuum boundary flux, and finite raw IBP to the continuum Green identity.
-/
structure AnalyticIntervalLiftConvergenceContract
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint) where
  ApproximationIndex : Type
  sample :
    ApproximationIndex ->
      ContinuumField ContinuumPoint ->
      ContinuumField TwoPointSpatialInterval
  reconstruct :
    ApproximationIndex ->
      ContinuumField TwoPointSpatialInterval ->
      ContinuumField ContinuumPoint
  graph_laplacian_action_to_continuum_laplacian : Prop
  finite_endpoint_flux_to_continuum_boundary_flux : Prop
  finite_raw_ibp_to_continuum_green_identity : Prop
  finite_pairing_to_continuum_pairing : Prop
  trace_normal_derivative_convergence : Prop
  domain_regular_for_limit_passage : Prop
  orientation_convention_compatible : Prop
  separating_test_class_for_limit : Prop
  contract_implies_raw_spatial_ibp :
    graph_laplacian_action_to_continuum_laplacian ->
    finite_pairing_to_continuum_pairing ->
    finite_raw_ibp_to_continuum_green_identity ->
    domain_regular_for_limit_passage ->
      RawSpatialIntegrationByPartsStatement
        target.continuum_problem
        target.continuum_raw_boundary_flux
  contract_implies_boundary_flux_representation :
    finite_endpoint_flux_to_continuum_boundary_flux ->
    trace_normal_derivative_convergence ->
    orientation_convention_compatible ->
      BoundaryFluxRepresentationStatement
        target.continuum_problem
        target.continuum_raw_boundary_flux

/--
Supplied analytic interval lift evidence.

This is the exact evidence that would discharge A2A15A1; the current repo only
records the contract and retains these analytic obligations.
-/
structure AnalyticIntervalLiftWitness
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target) where
  analytic_interval_domain_model_supplied :
    target.analytic_interval_domain_model
  continuum_derivative_laplacian_semantics_supplied :
    target.continuum_derivative_laplacian_semantics
  boundary_trace_normal_derivative_semantics_supplied :
    target.boundary_trace_normal_derivative_semantics
  target_domain_regular_for_limit_passage_supplied :
    target.domain_regular_for_limit_passage
  target_orientation_convention_for_limit_supplied :
    target.orientation_convention_for_limit
  graph_laplacian_action_convergence_supplied :
    contract.graph_laplacian_action_to_continuum_laplacian
  finite_endpoint_flux_convergence_supplied :
    contract.finite_endpoint_flux_to_continuum_boundary_flux
  finite_raw_ibp_green_identity_convergence_supplied :
    contract.finite_raw_ibp_to_continuum_green_identity
  finite_pairing_convergence_supplied :
    contract.finite_pairing_to_continuum_pairing
  trace_normal_derivative_convergence_supplied :
    contract.trace_normal_derivative_convergence
  contract_domain_regular_for_limit_passage_supplied :
    contract.domain_regular_for_limit_passage
  orientation_convention_compatible_supplied :
    contract.orientation_convention_compatible
  separating_test_class_for_limit_supplied :
    contract.separating_test_class_for_limit

/-- A supplied A2A15A1 witness gives continuum raw spatial IBP. -/
theorem analytic_interval_lift_witness_supplies_raw_ibp
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target)
    (witness : AnalyticIntervalLiftWitness target contract) :
    RawSpatialIntegrationByPartsStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux :=
  contract.contract_implies_raw_spatial_ibp
    witness.graph_laplacian_action_convergence_supplied
    witness.finite_pairing_convergence_supplied
    witness.finite_raw_ibp_green_identity_convergence_supplied
    witness.contract_domain_regular_for_limit_passage_supplied

/-- A supplied A2A15A1 witness represents finite endpoint flux in the limit. -/
theorem analytic_interval_lift_witness_supplies_boundary_flux_representation
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target)
    (witness : AnalyticIntervalLiftWitness target contract) :
    BoundaryFluxRepresentationStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux :=
  contract.contract_implies_boundary_flux_representation
    witness.finite_endpoint_flux_convergence_supplied
    witness.trace_normal_derivative_convergence_supplied
    witness.orientation_convention_compatible_supplied

/--
Supplied A2A15A1 evidence feeds the split A2A15 boundary-flux evidence route.
-/
def spatialBoundaryFluxSubblockerEvidenceOfAnalyticIntervalLiftWitness
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target)
    (witness : AnalyticIntervalLiftWitness target contract) :
    SpatialBoundaryFluxSubblockerEvidence
      target.continuum_problem where
  selected_problem := target.continuum_problem_selected
  raw_boundary_flux := target.continuum_raw_boundary_flux
  raw_spatial_integration_by_parts_source :=
    contract.graph_laplacian_action_to_continuum_laplacian ∧
      contract.finite_pairing_to_continuum_pairing ∧
      contract.finite_raw_ibp_to_continuum_green_identity ∧
      contract.domain_regular_for_limit_passage
  raw_spatial_integration_by_parts_source_supplied := by
    constructor
    · exact witness.graph_laplacian_action_convergence_supplied
    · constructor
      · exact witness.finite_pairing_convergence_supplied
      · constructor
        · exact witness.finite_raw_ibp_green_identity_convergence_supplied
        · exact witness.contract_domain_regular_for_limit_passage_supplied
  raw_spatial_integration_by_parts_statement :=
    analytic_interval_lift_witness_supplies_raw_ibp
      target contract witness
  boundary_flux_representation_source :=
    contract.finite_endpoint_flux_to_continuum_boundary_flux ∧
      contract.trace_normal_derivative_convergence ∧
      contract.orientation_convention_compatible
  boundary_flux_representation_source_supplied := by
    constructor
    · exact witness.finite_endpoint_flux_convergence_supplied
    · constructor
      · exact witness.trace_normal_derivative_convergence_supplied
      · exact witness.orientation_convention_compatible_supplied
  boundary_flux_representation_statement :=
    analytic_interval_lift_witness_supplies_boundary_flux_representation
      target contract witness
  regularity_domain_assumptions :=
    target.domain_regular_for_limit_passage ∧
      contract.domain_regular_for_limit_passage
  regularity_domain_assumptions_supplied := by
    constructor
    · exact witness.target_domain_regular_for_limit_passage_supplied
    · exact witness.contract_domain_regular_for_limit_passage_supplied
  trace_compatibility :=
    contract.finite_endpoint_flux_to_continuum_boundary_flux ∧
      contract.trace_normal_derivative_convergence
  trace_compatibility_supplied := by
    constructor
    · exact witness.finite_endpoint_flux_convergence_supplied
    · exact witness.trace_normal_derivative_convergence_supplied
  trace_normal_derivative_semantics :=
    target.boundary_trace_normal_derivative_semantics ∧
      contract.trace_normal_derivative_convergence
  trace_normal_derivative_semantics_supplied := by
    constructor
    · exact witness.boundary_trace_normal_derivative_semantics_supplied
    · exact witness.trace_normal_derivative_convergence_supplied
  orientation_convention :=
    target.orientation_convention_for_limit ∧
      contract.orientation_convention_compatible
  orientation_convention_supplied := by
    constructor
    · exact witness.target_orientation_convention_for_limit_supplied
    · exact witness.orientation_convention_compatible_supplied
  concrete_laplacian_construction :=
    target.continuum_derivative_laplacian_semantics ∧
      contract.graph_laplacian_action_to_continuum_laplacian
  concrete_laplacian_construction_supplied := by
    constructor
    · exact witness.continuum_derivative_laplacian_semantics_supplied
    · exact witness.graph_laplacian_action_convergence_supplied
  separating_test_class :=
    contract.separating_test_class_for_limit
  separating_test_class_supplied :=
    witness.separating_test_class_for_limit_supplied

/-- Supplied A2A15A1 evidence gives the A2A14 Green-identity statement. -/
theorem analytic_interval_lift_witness_feeds_a2a14
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target)
    (witness : AnalyticIntervalLiftWitness target contract) :
    SpatialLaplacianGreenIdentityStatement
      target.continuum_problem :=
  spatial_green_identity_statement_of_subblocker_evidence
    (spatialBoundaryFluxSubblockerEvidenceOfAnalyticIntervalLiftWitness
      target contract witness)

/-- Status readout for the retained A2A15A1 contract. -/
structure AnalyticIntervalLiftStatus where
  finite_two_point_raw_ibp_available :
    RawSpatialIntegrationByPartsStatement
      twoPointSpatialBoundaryProblem
      twoPointRawBoundaryFlux
  finite_two_point_flux_representation_available :
    BoundaryFluxRepresentationStatement
      twoPointSpatialBoundaryProblem
      twoPointRawBoundaryFlux
  finite_two_point_feeds_a2a14 :
    SpatialLaplacianGreenIdentityStatement
      twoPointSpatialBoundaryProblem
  analytic_interval_lift_statement_defined : Prop
  graph_laplacian_action_convergence_stated : Prop
  finite_endpoint_flux_convergence_stated : Prop
  finite_raw_ibp_green_identity_convergence_stated : Prop
  finite_pairing_convergence_stated : Prop
  trace_normal_derivative_convergence_stated : Prop
  analytic_interval_lift_closed : Prop
  analytic_interval_lift_not_closed :
    Not analytic_interval_lift_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status for the retained analytic interval lift contract. -/
def analyticIntervalLiftStatusV0 :
    AnalyticIntervalLiftStatus where
  finite_two_point_raw_ibp_available :=
    two_point_raw_spatial_integration_by_parts
  finite_two_point_flux_representation_available :=
    two_point_boundary_flux_representation
  finite_two_point_feeds_a2a14 :=
    two_point_spatial_green_identity_statement
  analytic_interval_lift_statement_defined := True
  graph_laplacian_action_convergence_stated := True
  finite_endpoint_flux_convergence_stated := True
  finite_raw_ibp_green_identity_convergence_stated := True
  finite_pairing_convergence_stated := True
  trace_normal_derivative_convergence_stated := True
  analytic_interval_lift_closed := False
  analytic_interval_lift_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A15ARawSpatialIBPProofContractRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId
  outcome_id := analyticIntervalLiftContractOutcomeId

/-- Short proof-facing status alias. -/
def analyticLiftStatusV0 : AnalyticIntervalLiftStatus :=
  analyticIntervalLiftStatusV0

/-- The finite raw-IBP theorem remains available to the lift contract. -/
theorem analytic_interval_lift_finite_raw_ibp_available_v0 :
    RawSpatialIntegrationByPartsStatement
      twoPointSpatialBoundaryProblem
      twoPointRawBoundaryFlux :=
  analyticLiftStatusV0.finite_two_point_raw_ibp_available

/-- The finite endpoint flux representation remains available. -/
theorem analytic_interval_lift_finite_flux_representation_available_v0 :
    BoundaryFluxRepresentationStatement
      twoPointSpatialBoundaryProblem
      twoPointRawBoundaryFlux :=
  analyticLiftStatusV0.finite_two_point_flux_representation_available

/-- The graph-Laplacian action convergence channel is stated. -/
theorem analytic_interval_lift_graph_action_convergence_stated_v0 :
    analyticLiftStatusV0.graph_laplacian_action_convergence_stated := by
  trivial

/-- The finite endpoint flux convergence channel is stated. -/
theorem analytic_interval_lift_endpoint_flux_convergence_stated_v0 :
    analyticLiftStatusV0.finite_endpoint_flux_convergence_stated := by
  trivial

/-- The finite raw-IBP to Green-identity convergence channel is stated. -/
theorem analytic_interval_lift_raw_ibp_green_identity_convergence_stated_v0 :
    analyticLiftStatusV0.finite_raw_ibp_green_identity_convergence_stated := by
  trivial

/-- The analytic interval lift is stated, but not closed. -/
theorem analytic_interval_lift_not_closed_v0 :
    Not analyticLiftStatusV0.analytic_interval_lift_closed := by
  exact analyticLiftStatusV0.analytic_interval_lift_not_closed

/-- The retained A2A15A1 lift contract does not authorize Phase 2. -/
theorem analytic_interval_lift_phase2_not_authorized_v0 :
    Not analyticLiftStatusV0.phase2Authorized := by
  exact analyticLiftStatusV0.phase2_not_authorized

/-- The retained A2A15A1 contract exposes its A2A15A parent blocker. -/
theorem analytic_interval_lift_parent_retained_id_v0 :
    analyticIntervalLiftStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A15ARawSpatialIBPProofContractRetainedId := by
  simp [analyticIntervalLiftStatusV0]

/-- The retained A2A15A1 contract exposes its retained blocker id. -/
theorem analytic_interval_lift_retained_id_v0 :
    analyticIntervalLiftStatusV0.retained_blocker_id =
      phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId := by
  simp [analyticIntervalLiftStatusV0]

/-- The retained A2A15A1 contract exposes its outcome id. -/
theorem analytic_interval_lift_outcome_id_v0 :
    analyticIntervalLiftStatusV0.outcome_id =
      analyticIntervalLiftContractOutcomeId := by
  simp [analyticIntervalLiftStatusV0]

end

end ContinuumSpatialAnalyticIntervalLift
end QFT
end ToeFormal
