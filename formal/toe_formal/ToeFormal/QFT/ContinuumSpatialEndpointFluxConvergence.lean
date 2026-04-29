/-
ToeFormal/QFT/ContinuumSpatialEndpointFluxConvergence.lean

Retained A2A15A1B finite endpoint-flux to continuum boundary-flux channel.

Scope:
- split the second A2A15A1 convergence channel into its own proof-facing
  surface
- isolate endpoint flux representation, continuum boundary trace and normal
  derivative semantics, orientation convention, boundary reconstruction
  compatibility, and flux-term convergence mode
- prove that supplied channel evidence fills the A2A15A1 analytic interval
  lift contract's endpoint-flux, trace-normal convergence, and orientation
  compatibility fields
- keep actual flux convergence, continuum boundary theorem, Phase 2
  authorization, seam closure, empirical validation, and master-action
  promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialAnalyticIntervalLift

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialEndpointFluxConvergence

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialLaplacianBoundaryFluxSubblockers
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialAnalyticIntervalLift

set_option autoImplicit false

noncomputable section

/-- Retained blocker for the A2A15A1B endpoint-flux channel. -/
def phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1B_FINITE_ENDPOINT_FLUX_TO_CONTINUUM_" ++
    "BOUNDARY_FLUX_RETAINED"

/-- Outcome id for the retained endpoint-flux convergence split. -/
def finiteEndpointFluxToContinuumBoundaryFluxSplitOutcomeId : String :=
  "A2A15A1B_FINITE_ENDPOINT_FLUX_TO_CONTINUUM_BOUNDARY_FLUX_" ++
    "CHANNEL_SPLIT_RETAINED"

/-- Remaining objects after the A2A15A1B channel split. -/
inductive Phase1Blocker003A2A15A1BEndpointFluxMissingObject where
  | endpointFluxRepresentation
  | continuumBoundaryTraceSemantics
  | continuumNormalDerivativeSemantics
  | orientationConvention
  | boundaryReconstructionCompatibility
  | fluxTermConvergenceMode
  | finiteEndpointFluxConsistencyTheorem
  | traceNormalDerivativeConvergence
  | orientationCompatibility
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A2A15A1B objects. -/
def phase1Blocker003A2A15A1BEndpointFluxMissingObjectId :
    Phase1Blocker003A2A15A1BEndpointFluxMissingObject -> String
  | .endpointFluxRepresentation =>
      "003A2A15A1B_ENDPOINT_FLUX_REPRESENTATION_RETAINED"
  | .continuumBoundaryTraceSemantics =>
      "003A2A15A1B_CONTINUUM_BOUNDARY_TRACE_SEMANTICS_RETAINED"
  | .continuumNormalDerivativeSemantics =>
      "003A2A15A1B_CONTINUUM_NORMAL_DERIVATIVE_SEMANTICS_RETAINED"
  | .orientationConvention =>
      "003A2A15A1B_ORIENTATION_CONVENTION_RETAINED"
  | .boundaryReconstructionCompatibility =>
      "003A2A15A1B_BOUNDARY_RECONSTRUCTION_COMPATIBILITY_RETAINED"
  | .fluxTermConvergenceMode =>
      "003A2A15A1B_FLUX_TERM_CONVERGENCE_MODE_RETAINED"
  | .finiteEndpointFluxConsistencyTheorem =>
      "003A2A15A1B_FINITE_ENDPOINT_FLUX_CONSISTENCY_THEOREM_RETAINED"
  | .traceNormalDerivativeConvergence =>
      "003A2A15A1B_TRACE_NORMAL_DERIVATIVE_CONVERGENCE_RETAINED"
  | .orientationCompatibility =>
      "003A2A15A1B_ORIENTATION_COMPATIBILITY_RETAINED"

/-- The retained A2A15A1B object list is stable and explicit. -/
def phase1Blocker003A2A15A1BEndpointFluxMissingObjectsV0 :
    List Phase1Blocker003A2A15A1BEndpointFluxMissingObject :=
  [ .endpointFluxRepresentation
  , .continuumBoundaryTraceSemantics
  , .continuumNormalDerivativeSemantics
  , .orientationConvention
  , .boundaryReconstructionCompatibility
  , .fluxTermConvergenceMode
  , .finiteEndpointFluxConsistencyTheorem
  , .traceNormalDerivativeConvergence
  , .orientationCompatibility
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a15a1b_missing_objects_v0_expected :
    phase1Blocker003A2A15A1BEndpointFluxMissingObjectsV0 =
      [ .endpointFluxRepresentation
      , .continuumBoundaryTraceSemantics
      , .continuumNormalDerivativeSemantics
      , .orientationConvention
      , .boundaryReconstructionCompatibility
      , .fluxTermConvergenceMode
      , .finiteEndpointFluxConsistencyTheorem
      , .traceNormalDerivativeConvergence
      , .orientationCompatibility
      ] := by
  rfl

/--
Evidence package for the endpoint-flux channel of the A2A15A1 lift.

The actual finite endpoint-flux to continuum boundary-flux theorem is supplied
by the caller. This surface records the analytic ingredients and the maps into
the parent A2A15A1 contract fields.
-/
structure FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target) where
  endpoint_flux_representation : Prop
  endpoint_flux_representation_supplied :
    endpoint_flux_representation
  continuum_boundary_trace_semantics : Prop
  continuum_boundary_trace_semantics_supplied :
    continuum_boundary_trace_semantics
  continuum_normal_derivative_semantics : Prop
  continuum_normal_derivative_semantics_supplied :
    continuum_normal_derivative_semantics
  orientation_convention : Prop
  orientation_convention_supplied : orientation_convention
  boundary_reconstruction_compatibility : Prop
  boundary_reconstruction_compatibility_supplied :
    boundary_reconstruction_compatibility
  flux_term_convergence_mode : Prop
  flux_term_convergence_mode_supplied :
    flux_term_convergence_mode
  finite_endpoint_flux_consistency_theorem : Prop
  finite_endpoint_flux_consistency_theorem_supplied :
    finite_endpoint_flux_consistency_theorem
  trace_normal_derivative_convergence_statement : Prop
  trace_normal_derivative_convergence_statement_supplied :
    trace_normal_derivative_convergence_statement
  orientation_compatibility_statement : Prop
  orientation_compatibility_statement_supplied :
    orientation_compatibility_statement
  semantics_supply_parent_boundary_trace_normal_derivative :
    continuum_boundary_trace_semantics ->
    continuum_normal_derivative_semantics ->
      target.boundary_trace_normal_derivative_semantics
  orientation_supplies_parent_orientation :
    orientation_convention ->
      target.orientation_convention_for_limit
  channel_supplies_parent_contract_field :
    endpoint_flux_representation ->
    continuum_boundary_trace_semantics ->
    continuum_normal_derivative_semantics ->
    orientation_convention ->
    boundary_reconstruction_compatibility ->
    flux_term_convergence_mode ->
    finite_endpoint_flux_consistency_theorem ->
      contract.finite_endpoint_flux_to_continuum_boundary_flux
  channel_supplies_parent_trace_normal_convergence :
    trace_normal_derivative_convergence_statement ->
    continuum_normal_derivative_semantics ->
      contract.trace_normal_derivative_convergence
  channel_supplies_parent_orientation_compatibility :
    orientation_compatibility_statement ->
    orientation_convention ->
      contract.orientation_convention_compatible

/-- Supplied A2A15A1B evidence fills the parent boundary trace semantics. -/
theorem endpoint_flux_channel_supplies_parent_boundary_trace_normal_derivative
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract) :
    target.boundary_trace_normal_derivative_semantics :=
  evidence.semantics_supply_parent_boundary_trace_normal_derivative
    evidence.continuum_boundary_trace_semantics_supplied
    evidence.continuum_normal_derivative_semantics_supplied

/-- Supplied A2A15A1B evidence fills the parent orientation convention. -/
theorem endpoint_flux_channel_supplies_parent_orientation
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract) :
    target.orientation_convention_for_limit :=
  evidence.orientation_supplies_parent_orientation
    evidence.orientation_convention_supplied

/-- Supplied A2A15A1B evidence fills the parent endpoint-flux field. -/
theorem endpoint_flux_channel_supplies_parent_contract_field
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract) :
    contract.finite_endpoint_flux_to_continuum_boundary_flux :=
  evidence.channel_supplies_parent_contract_field
    evidence.endpoint_flux_representation_supplied
    evidence.continuum_boundary_trace_semantics_supplied
    evidence.continuum_normal_derivative_semantics_supplied
    evidence.orientation_convention_supplied
    evidence.boundary_reconstruction_compatibility_supplied
    evidence.flux_term_convergence_mode_supplied
    evidence.finite_endpoint_flux_consistency_theorem_supplied

/-- Supplied A2A15A1B evidence fills parent trace-normal convergence. -/
theorem endpoint_flux_channel_supplies_parent_trace_normal_convergence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract) :
    contract.trace_normal_derivative_convergence :=
  evidence.channel_supplies_parent_trace_normal_convergence
    evidence.trace_normal_derivative_convergence_statement_supplied
    evidence.continuum_normal_derivative_semantics_supplied

/-- Supplied A2A15A1B evidence fills parent orientation compatibility. -/
theorem endpoint_flux_channel_supplies_parent_orientation_compatibility
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract) :
    contract.orientation_convention_compatible :=
  evidence.channel_supplies_parent_orientation_compatibility
    evidence.orientation_compatibility_statement_supplied
    evidence.orientation_convention_supplied

/--
Combine the endpoint-flux channel with the remaining A2A15A1 evidence fields to
recover the parent analytic-interval-lift witness.
-/
def analyticIntervalLiftWitnessOfEndpointFluxChannelEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract)
    (analyticInterval : target.analytic_interval_domain_model)
    (derivativeLaplacian :
      target.continuum_derivative_laplacian_semantics)
    (targetDomain : target.domain_regular_for_limit_passage)
    (graphAction :
      contract.graph_laplacian_action_to_continuum_laplacian)
    (finiteRawIBPGreen :
      contract.finite_raw_ibp_to_continuum_green_identity)
    (finitePairing : contract.finite_pairing_to_continuum_pairing)
    (contractDomain : contract.domain_regular_for_limit_passage)
    (separating : contract.separating_test_class_for_limit) :
    AnalyticIntervalLiftWitness target contract where
  analytic_interval_domain_model_supplied := analyticInterval
  continuum_derivative_laplacian_semantics_supplied := derivativeLaplacian
  boundary_trace_normal_derivative_semantics_supplied :=
    endpoint_flux_channel_supplies_parent_boundary_trace_normal_derivative
      evidence
  target_domain_regular_for_limit_passage_supplied := targetDomain
  target_orientation_convention_for_limit_supplied :=
    endpoint_flux_channel_supplies_parent_orientation evidence
  graph_laplacian_action_convergence_supplied := graphAction
  finite_endpoint_flux_convergence_supplied :=
    endpoint_flux_channel_supplies_parent_contract_field evidence
  finite_raw_ibp_green_identity_convergence_supplied := finiteRawIBPGreen
  finite_pairing_convergence_supplied := finitePairing
  trace_normal_derivative_convergence_supplied :=
    endpoint_flux_channel_supplies_parent_trace_normal_convergence evidence
  contract_domain_regular_for_limit_passage_supplied := contractDomain
  orientation_convention_compatible_supplied :=
    endpoint_flux_channel_supplies_parent_orientation_compatibility evidence
  separating_test_class_for_limit_supplied := separating

/-- Supplied A2A15A1B evidence plus remaining lift fields feeds A2A14. -/
theorem endpoint_flux_channel_feeds_a2a14_given_remaining_lift_evidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target contract)
    (analyticInterval : target.analytic_interval_domain_model)
    (derivativeLaplacian :
      target.continuum_derivative_laplacian_semantics)
    (targetDomain : target.domain_regular_for_limit_passage)
    (graphAction :
      contract.graph_laplacian_action_to_continuum_laplacian)
    (finiteRawIBPGreen :
      contract.finite_raw_ibp_to_continuum_green_identity)
    (finitePairing : contract.finite_pairing_to_continuum_pairing)
    (contractDomain : contract.domain_regular_for_limit_passage)
    (separating : contract.separating_test_class_for_limit) :
    SpatialLaplacianGreenIdentityStatement target.continuum_problem :=
  analytic_interval_lift_witness_feeds_a2a14 target contract
    (analyticIntervalLiftWitnessOfEndpointFluxChannelEvidence
      evidence analyticInterval derivativeLaplacian targetDomain graphAction
      finiteRawIBPGreen finitePairing contractDomain separating)

/-- Status readout for the retained A2A15A1B channel split. -/
structure FiniteEndpointFluxToContinuumBoundaryFluxChannelStatus where
  parent_analytic_interval_lift_contract_defined : Prop
  endpoint_flux_channel_split_defined : Prop
  endpoint_flux_representation_stated : Prop
  continuum_boundary_trace_semantics_stated : Prop
  continuum_normal_derivative_semantics_stated : Prop
  orientation_convention_stated : Prop
  boundary_reconstruction_compatibility_stated : Prop
  flux_term_convergence_mode_stated : Prop
  endpoint_flux_convergence_closed : Prop
  endpoint_flux_convergence_not_closed :
    Not endpoint_flux_convergence_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status for the retained endpoint-flux channel split. -/
def finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0 :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelStatus where
  parent_analytic_interval_lift_contract_defined := True
  endpoint_flux_channel_split_defined := True
  endpoint_flux_representation_stated := True
  continuum_boundary_trace_semantics_stated := True
  continuum_normal_derivative_semantics_stated := True
  orientation_convention_stated := True
  boundary_reconstruction_compatibility_stated := True
  flux_term_convergence_mode_stated := True
  endpoint_flux_convergence_closed := False
  endpoint_flux_convergence_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId
  outcome_id := finiteEndpointFluxToContinuumBoundaryFluxSplitOutcomeId

/-- Short proof-facing status alias. -/
def endpointFluxChannelStatusV0 :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelStatus :=
  finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0

/-- The endpoint-flux channel has been split and stated. -/
theorem endpoint_flux_channel_split_defined_v0 :
    endpointFluxChannelStatusV0.endpoint_flux_channel_split_defined := by
  trivial

/-- The endpoint-flux representation object is stated. -/
theorem endpoint_flux_channel_endpoint_representation_stated_v0 :
    endpointFluxChannelStatusV0.endpoint_flux_representation_stated := by
  trivial

/-- The continuum boundary-trace semantics object is stated. -/
theorem endpoint_flux_channel_boundary_trace_stated_v0 :
    endpointFluxChannelStatusV0.continuum_boundary_trace_semantics_stated := by
  trivial

/-- The continuum normal-derivative semantics object is stated. -/
theorem endpoint_flux_channel_normal_derivative_stated_v0 :
    endpointFluxChannelStatusV0.continuum_normal_derivative_semantics_stated := by
  trivial

/-- The orientation convention object is stated. -/
theorem endpoint_flux_channel_orientation_stated_v0 :
    endpointFluxChannelStatusV0.orientation_convention_stated := by
  trivial

/-- The boundary reconstruction compatibility object is stated. -/
theorem endpoint_flux_channel_boundary_reconstruction_stated_v0 :
    endpointFluxChannelStatusV0.boundary_reconstruction_compatibility_stated := by
  trivial

/-- The flux-term convergence mode object is stated. -/
theorem endpoint_flux_channel_convergence_mode_stated_v0 :
    endpointFluxChannelStatusV0.flux_term_convergence_mode_stated := by
  trivial

/-- The endpoint-flux convergence theorem remains retained. -/
theorem endpoint_flux_channel_convergence_not_closed_v0 :
    Not endpointFluxChannelStatusV0.endpoint_flux_convergence_closed := by
  exact endpointFluxChannelStatusV0.endpoint_flux_convergence_not_closed

/-- The retained endpoint-flux channel does not authorize Phase 2. -/
theorem endpoint_flux_channel_phase2_not_authorized_v0 :
    Not endpointFluxChannelStatusV0.phase2Authorized := by
  exact endpointFluxChannelStatusV0.phase2_not_authorized

/-- The retained endpoint-flux channel exposes its parent A2A15A1 blocker. -/
theorem endpoint_flux_channel_parent_retained_id_v0 :
    finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId := by
  simp [finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0]

/-- The retained endpoint-flux channel exposes its retained blocker id. -/
theorem endpoint_flux_channel_retained_id_v0 :
    finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0.retained_blocker_id =
      phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId := by
  simp [finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0]

/-- The retained endpoint-flux channel exposes its outcome id. -/
theorem endpoint_flux_channel_outcome_id_v0 :
    finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0.outcome_id =
      finiteEndpointFluxToContinuumBoundaryFluxSplitOutcomeId := by
  simp [finiteEndpointFluxToContinuumBoundaryFluxChannelStatusV0]

end

end ContinuumSpatialEndpointFluxConvergence
end QFT
end ToeFormal
