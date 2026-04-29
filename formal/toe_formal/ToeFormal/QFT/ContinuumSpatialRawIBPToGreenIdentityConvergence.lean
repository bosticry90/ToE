/-
ToeFormal/QFT/ContinuumSpatialRawIBPToGreenIdentityConvergence.lean

Retained A2A15A1C finite raw-IBP to continuum Green-identity channel.

Scope:
- split the third A2A15A1 convergence channel into its own proof-facing
  surface
- isolate finite raw IBP, continuum Green identity, the transfer rule, A1A/A1B
  dependencies, operator/flux convergence compatibility, pairing/domain
  compatibility, and the Green-identity convergence mode
- prove that supplied channel evidence fills the A2A15A1 analytic interval
  lift contract's finite raw-IBP to continuum Green-identity field
- keep actual finite-to-continuum Green-identity convergence, continuum
  closure, Phase 2 authorization, seam closure, empirical validation, and
  master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianConvergence
import ToeFormal.QFT.ContinuumSpatialEndpointFluxConvergence

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialRawIBPToGreenIdentityConvergence

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialLaplacianBoundaryFluxSubblockers
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialEndpointFluxConvergence

set_option autoImplicit false

noncomputable section

/-- Retained blocker for the A2A15A1C raw-IBP/Green-identity channel. -/
def phase1Blocker003A2A15A1CFiniteRawIBPToContinuumGreenIdentityRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1C_FINITE_RAW_IBP_TO_CONTINUUM_" ++
    "GREEN_IDENTITY_RETAINED"

/-- Outcome id for the retained raw-IBP/Green-identity convergence split. -/
def finiteRawIBPToContinuumGreenIdentitySplitOutcomeId : String :=
  "A2A15A1C_FINITE_RAW_IBP_TO_CONTINUUM_GREEN_IDENTITY_" ++
    "CHANNEL_SPLIT_RETAINED"

/-- Remaining objects after the A2A15A1C channel split. -/
inductive Phase1Blocker003A2A15A1CRawIBPGreenMissingObject where
  | finiteRawIBPStatement
  | continuumGreenIdentityStatement
  | finiteToContinuumIdentityTransferRule
  | graphLaplacianChannelDependency
  | endpointFluxChannelDependency
  | operatorFluxConvergenceCompatibility
  | pairingConvergenceCompatibility
  | domainRegularityForIdentityLimit
  | greenIdentityConvergenceMode
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A2A15A1C objects. -/
def phase1Blocker003A2A15A1CRawIBPGreenMissingObjectId :
    Phase1Blocker003A2A15A1CRawIBPGreenMissingObject -> String
  | .finiteRawIBPStatement =>
      "003A2A15A1C_FINITE_RAW_IBP_STATEMENT_RETAINED"
  | .continuumGreenIdentityStatement =>
      "003A2A15A1C_CONTINUUM_GREEN_IDENTITY_STATEMENT_RETAINED"
  | .finiteToContinuumIdentityTransferRule =>
      "003A2A15A1C_FINITE_TO_CONTINUUM_IDENTITY_TRANSFER_RULE_RETAINED"
  | .graphLaplacianChannelDependency =>
      "003A2A15A1C_GRAPH_LAPLACIAN_CHANNEL_DEPENDENCY_RETAINED"
  | .endpointFluxChannelDependency =>
      "003A2A15A1C_ENDPOINT_FLUX_CHANNEL_DEPENDENCY_RETAINED"
  | .operatorFluxConvergenceCompatibility =>
      "003A2A15A1C_OPERATOR_FLUX_CONVERGENCE_COMPATIBILITY_RETAINED"
  | .pairingConvergenceCompatibility =>
      "003A2A15A1C_PAIRING_CONVERGENCE_COMPATIBILITY_RETAINED"
  | .domainRegularityForIdentityLimit =>
      "003A2A15A1C_DOMAIN_REGULARITY_FOR_IDENTITY_LIMIT_RETAINED"
  | .greenIdentityConvergenceMode =>
      "003A2A15A1C_GREEN_IDENTITY_CONVERGENCE_MODE_RETAINED"

/-- The retained A2A15A1C object list is stable and explicit. -/
def phase1Blocker003A2A15A1CRawIBPGreenMissingObjectsV0 :
    List Phase1Blocker003A2A15A1CRawIBPGreenMissingObject :=
  [ .finiteRawIBPStatement
  , .continuumGreenIdentityStatement
  , .finiteToContinuumIdentityTransferRule
  , .graphLaplacianChannelDependency
  , .endpointFluxChannelDependency
  , .operatorFluxConvergenceCompatibility
  , .pairingConvergenceCompatibility
  , .domainRegularityForIdentityLimit
  , .greenIdentityConvergenceMode
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a15a1c_missing_objects_v0_expected :
    phase1Blocker003A2A15A1CRawIBPGreenMissingObjectsV0 =
      [ .finiteRawIBPStatement
      , .continuumGreenIdentityStatement
      , .finiteToContinuumIdentityTransferRule
      , .graphLaplacianChannelDependency
      , .endpointFluxChannelDependency
      , .operatorFluxConvergenceCompatibility
      , .pairingConvergenceCompatibility
      , .domainRegularityForIdentityLimit
      , .greenIdentityConvergenceMode
      ] := by
  rfl

/--
Evidence package for the finite raw-IBP to continuum Green-identity channel.

The finite-to-continuum Green-identity theorem itself is supplied by the
caller. This surface records the finite statement, continuum statement,
transfer rule, A1A/A1B dependencies, and compatibility requirements needed to
fill the parent A2A15A1 contract field.
-/
structure FiniteRawIBPToContinuumGreenIdentityChannelEvidence
    {ContinuumPoint : Type}
    (target : AnalyticIntervalLiftTarget ContinuumPoint)
    (contract : AnalyticIntervalLiftConvergenceContract target) where
  graph_channel :
    GraphLaplacianToContinuumLaplacianChannelEvidence target contract
  endpoint_flux_channel :
    FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence target contract
  finite_raw_ibp_statement : Prop
  finite_raw_ibp_statement_supplied :
    finite_raw_ibp_statement
  continuum_green_identity_statement : Prop
  continuum_green_identity_statement_supplied :
    continuum_green_identity_statement
  finite_to_continuum_identity_transfer_rule : Prop
  finite_to_continuum_identity_transfer_rule_supplied :
    finite_to_continuum_identity_transfer_rule
  operator_flux_convergence_compatibility : Prop
  operator_flux_convergence_compatibility_supplied :
    operator_flux_convergence_compatibility
  pairing_convergence_compatibility : Prop
  pairing_convergence_compatibility_supplied :
    pairing_convergence_compatibility
  domain_regular_for_identity_limit : Prop
  domain_regular_for_identity_limit_supplied :
    domain_regular_for_identity_limit
  green_identity_convergence_mode : Prop
  green_identity_convergence_mode_supplied :
    green_identity_convergence_mode
  channel_supplies_parent_contract_field :
    finite_raw_ibp_statement ->
    continuum_green_identity_statement ->
    finite_to_continuum_identity_transfer_rule ->
    contract.graph_laplacian_action_to_continuum_laplacian ->
    contract.finite_endpoint_flux_to_continuum_boundary_flux ->
    operator_flux_convergence_compatibility ->
    pairing_convergence_compatibility ->
    domain_regular_for_identity_limit ->
    green_identity_convergence_mode ->
      contract.finite_raw_ibp_to_continuum_green_identity
  pairing_compatibility_supplies_parent_pairing :
    pairing_convergence_compatibility ->
      contract.finite_pairing_to_continuum_pairing
  domain_regular_supplies_parent_target_domain :
    domain_regular_for_identity_limit ->
      target.domain_regular_for_limit_passage
  domain_regular_supplies_parent_contract_domain :
    domain_regular_for_identity_limit ->
      contract.domain_regular_for_limit_passage

/-- Supplied A2A15A1C evidence fills the parent raw-IBP/Green field. -/
theorem raw_ibp_green_channel_supplies_parent_contract_field
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract) :
    contract.finite_raw_ibp_to_continuum_green_identity :=
  evidence.channel_supplies_parent_contract_field
    evidence.finite_raw_ibp_statement_supplied
    evidence.continuum_green_identity_statement_supplied
    evidence.finite_to_continuum_identity_transfer_rule_supplied
    (graph_laplacian_channel_supplies_parent_contract_field
      evidence.graph_channel)
    (endpoint_flux_channel_supplies_parent_contract_field
      evidence.endpoint_flux_channel)
    evidence.operator_flux_convergence_compatibility_supplied
    evidence.pairing_convergence_compatibility_supplied
    evidence.domain_regular_for_identity_limit_supplied
    evidence.green_identity_convergence_mode_supplied

/-- Supplied A2A15A1C evidence fills parent finite-pairing convergence. -/
theorem raw_ibp_green_channel_supplies_parent_pairing
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract) :
    contract.finite_pairing_to_continuum_pairing :=
  evidence.pairing_compatibility_supplies_parent_pairing
    evidence.pairing_convergence_compatibility_supplied

/-- Supplied A2A15A1C evidence fills the target domain-regularity field. -/
theorem raw_ibp_green_channel_supplies_parent_target_domain
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract) :
    target.domain_regular_for_limit_passage :=
  evidence.domain_regular_supplies_parent_target_domain
    evidence.domain_regular_for_identity_limit_supplied

/-- Supplied A2A15A1C evidence fills the contract domain-regularity field. -/
theorem raw_ibp_green_channel_supplies_parent_contract_domain
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract) :
    contract.domain_regular_for_limit_passage :=
  evidence.domain_regular_supplies_parent_contract_domain
    evidence.domain_regular_for_identity_limit_supplied

/--
Combine the A1C channel with an analytic interval domain and separating test
class to recover the parent analytic-interval-lift witness.
-/
def analyticIntervalLiftWitnessOfRawIBPGreenChannelEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract)
    (analyticInterval : target.analytic_interval_domain_model)
    (separating : contract.separating_test_class_for_limit) :
    AnalyticIntervalLiftWitness target contract where
  analytic_interval_domain_model_supplied := analyticInterval
  continuum_derivative_laplacian_semantics_supplied :=
    graph_laplacian_channel_supplies_parent_derivative_laplacian_semantics
      evidence.graph_channel
  boundary_trace_normal_derivative_semantics_supplied :=
    endpoint_flux_channel_supplies_parent_boundary_trace_normal_derivative
      evidence.endpoint_flux_channel
  target_domain_regular_for_limit_passage_supplied :=
    raw_ibp_green_channel_supplies_parent_target_domain evidence
  target_orientation_convention_for_limit_supplied :=
    endpoint_flux_channel_supplies_parent_orientation
      evidence.endpoint_flux_channel
  graph_laplacian_action_convergence_supplied :=
    graph_laplacian_channel_supplies_parent_contract_field
      evidence.graph_channel
  finite_endpoint_flux_convergence_supplied :=
    endpoint_flux_channel_supplies_parent_contract_field
      evidence.endpoint_flux_channel
  finite_raw_ibp_green_identity_convergence_supplied :=
    raw_ibp_green_channel_supplies_parent_contract_field evidence
  finite_pairing_convergence_supplied :=
    raw_ibp_green_channel_supplies_parent_pairing evidence
  trace_normal_derivative_convergence_supplied :=
    endpoint_flux_channel_supplies_parent_trace_normal_convergence
      evidence.endpoint_flux_channel
  contract_domain_regular_for_limit_passage_supplied :=
    raw_ibp_green_channel_supplies_parent_contract_domain evidence
  orientation_convention_compatible_supplied :=
    endpoint_flux_channel_supplies_parent_orientation_compatibility
      evidence.endpoint_flux_channel
  separating_test_class_for_limit_supplied := separating

/-- Supplied A2A15A1C evidence plus remaining lift fields feeds A2A14. -/
theorem raw_ibp_green_channel_feeds_a2a14_given_remaining_lift_evidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {contract : AnalyticIntervalLiftConvergenceContract target}
    (evidence :
      FiniteRawIBPToContinuumGreenIdentityChannelEvidence
        target contract)
    (analyticInterval : target.analytic_interval_domain_model)
    (separating : contract.separating_test_class_for_limit) :
    SpatialLaplacianGreenIdentityStatement target.continuum_problem :=
  analytic_interval_lift_witness_feeds_a2a14 target contract
    (analyticIntervalLiftWitnessOfRawIBPGreenChannelEvidence
      evidence analyticInterval separating)

/-- Status readout for the retained A2A15A1C channel split. -/
structure FiniteRawIBPToContinuumGreenIdentityChannelStatus where
  parent_analytic_interval_lift_contract_defined : Prop
  raw_ibp_green_identity_channel_split_defined : Prop
  finite_raw_ibp_statement_stated : Prop
  continuum_green_identity_statement_stated : Prop
  finite_to_continuum_transfer_rule_stated : Prop
  graph_laplacian_channel_dependency_stated : Prop
  endpoint_flux_channel_dependency_stated : Prop
  operator_flux_compatibility_stated : Prop
  pairing_compatibility_stated : Prop
  domain_regular_for_identity_limit_stated : Prop
  green_identity_convergence_mode_stated : Prop
  raw_ibp_green_identity_convergence_closed : Prop
  raw_ibp_green_identity_convergence_not_closed :
    Not raw_ibp_green_identity_convergence_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  graph_channel_retained_blocker_id : String
  endpoint_flux_channel_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status for the retained raw-IBP/Green-identity channel split. -/
def finiteRawIBPToContinuumGreenIdentityChannelStatusV0 :
    FiniteRawIBPToContinuumGreenIdentityChannelStatus where
  parent_analytic_interval_lift_contract_defined := True
  raw_ibp_green_identity_channel_split_defined := True
  finite_raw_ibp_statement_stated := True
  continuum_green_identity_statement_stated := True
  finite_to_continuum_transfer_rule_stated := True
  graph_laplacian_channel_dependency_stated := True
  endpoint_flux_channel_dependency_stated := True
  operator_flux_compatibility_stated := True
  pairing_compatibility_stated := True
  domain_regular_for_identity_limit_stated := True
  green_identity_convergence_mode_stated := True
  raw_ibp_green_identity_convergence_closed := False
  raw_ibp_green_identity_convergence_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId
  graph_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  endpoint_flux_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1CFiniteRawIBPToContinuumGreenIdentityRetainedId
  outcome_id := finiteRawIBPToContinuumGreenIdentitySplitOutcomeId

/-- Short proof-facing status alias. -/
def rawIBPGreenChannelStatusV0 :
    FiniteRawIBPToContinuumGreenIdentityChannelStatus :=
  finiteRawIBPToContinuumGreenIdentityChannelStatusV0

/-- The raw-IBP/Green-identity channel has been split and stated. -/
theorem raw_ibp_green_channel_split_defined_v0 :
    rawIBPGreenChannelStatusV0.raw_ibp_green_identity_channel_split_defined := by
  trivial

/-- The finite raw-IBP statement object is stated. -/
theorem raw_ibp_green_channel_finite_raw_ibp_stated_v0 :
    rawIBPGreenChannelStatusV0.finite_raw_ibp_statement_stated := by
  trivial

/-- The continuum Green-identity statement object is stated. -/
theorem raw_ibp_green_channel_continuum_green_stated_v0 :
    rawIBPGreenChannelStatusV0.continuum_green_identity_statement_stated := by
  trivial

/-- The finite-to-continuum transfer rule object is stated. -/
theorem raw_ibp_green_channel_transfer_rule_stated_v0 :
    rawIBPGreenChannelStatusV0.finite_to_continuum_transfer_rule_stated := by
  trivial

/-- The A1A graph-Laplacian channel dependency is stated. -/
theorem raw_ibp_green_channel_graph_dependency_stated_v0 :
    rawIBPGreenChannelStatusV0.graph_laplacian_channel_dependency_stated := by
  trivial

/-- The A1B endpoint-flux channel dependency is stated. -/
theorem raw_ibp_green_channel_endpoint_flux_dependency_stated_v0 :
    rawIBPGreenChannelStatusV0.endpoint_flux_channel_dependency_stated := by
  trivial

/-- The operator/flux compatibility object is stated. -/
theorem raw_ibp_green_channel_operator_flux_compatibility_stated_v0 :
    rawIBPGreenChannelStatusV0.operator_flux_compatibility_stated := by
  trivial

/-- The pairing compatibility object is stated. -/
theorem raw_ibp_green_channel_pairing_compatibility_stated_v0 :
    rawIBPGreenChannelStatusV0.pairing_compatibility_stated := by
  trivial

/-- The Green-identity convergence theorem remains retained. -/
theorem raw_ibp_green_channel_convergence_not_closed_v0 :
    Not rawIBPGreenChannelStatusV0.raw_ibp_green_identity_convergence_closed := by
  exact rawIBPGreenChannelStatusV0.raw_ibp_green_identity_convergence_not_closed

/-- The retained raw-IBP/Green channel does not authorize Phase 2. -/
theorem raw_ibp_green_channel_phase2_not_authorized_v0 :
    Not rawIBPGreenChannelStatusV0.phase2Authorized := by
  exact rawIBPGreenChannelStatusV0.phase2_not_authorized

/-- The retained raw-IBP/Green channel exposes its parent A2A15A1 blocker. -/
theorem raw_ibp_green_channel_parent_retained_id_v0 :
    finiteRawIBPToContinuumGreenIdentityChannelStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A15A1AnalyticIntervalLiftRetainedId := by
  simp [finiteRawIBPToContinuumGreenIdentityChannelStatusV0]

/-- The retained raw-IBP/Green channel exposes its A1A blocker dependency. -/
theorem raw_ibp_green_channel_graph_dependency_id_v0 :
    finiteRawIBPToContinuumGreenIdentityChannelStatusV0.graph_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  simp [finiteRawIBPToContinuumGreenIdentityChannelStatusV0]

/-- The retained raw-IBP/Green channel exposes its A1B blocker dependency. -/
theorem raw_ibp_green_channel_endpoint_flux_dependency_id_v0 :
    finiteRawIBPToContinuumGreenIdentityChannelStatusV0.endpoint_flux_channel_retained_blocker_id =
      phase1Blocker003A2A15A1BFiniteEndpointFluxToContinuumBoundaryFluxRetainedId := by
  simp [finiteRawIBPToContinuumGreenIdentityChannelStatusV0]

/-- The retained raw-IBP/Green channel exposes its retained blocker id. -/
theorem raw_ibp_green_channel_retained_id_v0 :
    finiteRawIBPToContinuumGreenIdentityChannelStatusV0.retained_blocker_id =
      phase1Blocker003A2A15A1CFiniteRawIBPToContinuumGreenIdentityRetainedId := by
  simp [finiteRawIBPToContinuumGreenIdentityChannelStatusV0]

/-- The retained raw-IBP/Green channel exposes its outcome id. -/
theorem raw_ibp_green_channel_outcome_id_v0 :
    finiteRawIBPToContinuumGreenIdentityChannelStatusV0.outcome_id =
      finiteRawIBPToContinuumGreenIdentitySplitOutcomeId := by
  simp [finiteRawIBPToContinuumGreenIdentityChannelStatusV0]

end

end ContinuumSpatialRawIBPToGreenIdentityConvergence
end QFT
end ToeFormal
