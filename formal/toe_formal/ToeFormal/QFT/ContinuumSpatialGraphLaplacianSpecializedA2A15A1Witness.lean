/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness.lean

A1A22 specialized A2A15A1 witness attempt after the A1A21 parent
graph-channel interface refactor.

Scope:
- construct an `AnalyticIntervalLiftWitness` from the A1A21 specialized
  parent graph-channel contract when all remaining non-graph A2A15A1 evidence
  fields are supplied
- prove the specialized graph slot is no longer the witness blocker
- record the evidence-free obstruction: endpoint-flux and other non-graph
  witness fields remain independent obligations
- retain A2A15A1 closure, A2A15 closure, and Phase 2 authorization
- make no Phase 0-5 objective-completion claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A22 specialized A2A15A1 witness attempt. -/
def a1a22SpecializedA2A15A1WitnessSurfaceId : String :=
  "A2A15A1A22_SPECIALIZED_A2A15A1_WITNESS"

/-- Retained blocker after the specialized witness attempt. -/
def phase1Blocker003A2A15A1A22SpecializedA2A15A1WitnessRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A22_SPECIALIZED_A2A15A1_" ++
    "WITNESS_RETAINED"

/-- Outcome id for the retained A1A22 specialized witness slice. -/
def specializedA2A15A1WitnessRetainedOutcomeId : String :=
  "SPECIALIZED_A2A15A1_WITNESS_RETAINED"

/--
The remaining non-graph evidence required to turn the A1A21 specialized
contract into a full A2A15A1 analytic-interval lift witness.

The graph-channel evidence is deliberately absent from this structure: it is
supplied by A1A16 through the A1A21 specialized graph slot.
-/
structure SpecializedA2A15A1RemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C) where
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

/--
Conditional specialized A2A15A1 witness constructor.

A1A21/A1A16 provide the graph-Laplacian field; the remaining evidence object
supplies exactly the non-graph fields still needed by the parent lift witness.
-/
def specializedA2A15A1WitnessOfRemainingEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1RemainingEvidence contract) :
    AnalyticIntervalLiftWitness
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) where
  analytic_interval_domain_model_supplied :=
    remaining.analytic_interval_domain_model_supplied
  continuum_derivative_laplacian_semantics_supplied :=
    remaining.continuum_derivative_laplacian_semantics_supplied
  boundary_trace_normal_derivative_semantics_supplied :=
    remaining.boundary_trace_normal_derivative_semantics_supplied
  target_domain_regular_for_limit_passage_supplied :=
    remaining.target_domain_regular_for_limit_passage_supplied
  target_orientation_convention_for_limit_supplied :=
    remaining.target_orientation_convention_for_limit_supplied
  graph_laplacian_action_convergence_supplied :=
    actual_error_supplies_specialized_parent_graph_field_v0 contract
  finite_endpoint_flux_convergence_supplied :=
    remaining.finite_endpoint_flux_convergence_supplied
  finite_raw_ibp_green_identity_convergence_supplied :=
    remaining.finite_raw_ibp_green_identity_convergence_supplied
  finite_pairing_convergence_supplied :=
    remaining.finite_pairing_convergence_supplied
  trace_normal_derivative_convergence_supplied :=
    remaining.trace_normal_derivative_convergence_supplied
  contract_domain_regular_for_limit_passage_supplied :=
    remaining.contract_domain_regular_for_limit_passage_supplied
  orientation_convention_compatible_supplied :=
    remaining.orientation_convention_compatible_supplied
  separating_test_class_for_limit_supplied :=
    remaining.separating_test_class_for_limit_supplied

/-- The specialized conditional witness supplies continuum raw spatial IBP. -/
theorem specialized_a2a15a1_witness_supplies_raw_ibp_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1RemainingEvidence contract) :
    RawSpatialIntegrationByPartsStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux := by
  exact
    analytic_interval_lift_witness_supplies_raw_ibp
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract)
      (specializedA2A15A1WitnessOfRemainingEvidence
        contract remaining)

/-- The specialized conditional witness feeds the A2A14 Green-identity route. -/
theorem specialized_a2a15a1_witness_feeds_a2a14_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (remaining :
      SpecializedA2A15A1RemainingEvidence contract) :
    SpatialLaplacianGreenIdentityStatement target.continuum_problem := by
  exact
    analytic_interval_lift_witness_feeds_a2a14
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract)
      (specializedA2A15A1WitnessOfRemainingEvidence
        contract remaining)

/--
A legal specialized contract can still leave the endpoint-flux channel false.

This is the concrete obstruction showing that A1A21's graph specialization
alone cannot manufacture a full A2A15A1 witness.
-/
def specializedParentContractWithFalseEndpointFlux
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    ActualErrorSpecializedParentGraphChannelContract
      (f := f) target x C where
  evidenceOnly := evidenceOnly
  ApproximationIndex := Unit
  sample := fun _ _ _ => 0
  reconstruct := fun _ _ _ => 0
  finite_endpoint_flux_to_continuum_boundary_flux := False
  finite_raw_ibp_to_continuum_green_identity := False
  finite_pairing_to_continuum_pairing := False
  trace_normal_derivative_convergence := False
  domain_regular_for_limit_passage := False
  orientation_convention_compatible := False
  separating_test_class_for_limit := False
  contract_implies_raw_spatial_ibp := by
    intro _ hPairing _ _
    exact False.elim hPairing
  contract_implies_boundary_flux_representation := by
    intro hEndpointFlux _ _
    exact False.elim hEndpointFlux

/-- The false-endpoint specialized contract cannot have an A2A15A1 witness. -/
theorem specialized_false_endpoint_contract_has_no_a2a15a1_witness_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    Not
      (AnalyticIntervalLiftWitness
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          (specializedParentContractWithFalseEndpointFlux
            (target := target) evidenceOnly))) := by
  intro witness
  exact witness.finite_endpoint_flux_convergence_supplied

/-- Remaining objects after the A1A22 specialized witness attempt. -/
inductive SpecializedA2A15A1WitnessObstruction where
  | noRemainingNonGraphEvidencePackage
  | noFiniteEndpointFluxClosure
  | noFiniteRawIBPGreenIdentityClosure
  | noFinitePairingConvergence
  | noTraceNormalDerivativeConvergence
  | noDomainRegularityForLimitPassage
  | noOrientationCompatibility
  | noSeparatingTestClassForLimit
  | noTargetContinuumSemanticsPackage
  | noA2A15BoundaryFluxClosure
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A22 objects. -/
def specializedA2A15A1WitnessObstructionId :
    SpecializedA2A15A1WitnessObstruction -> String
  | .noRemainingNonGraphEvidencePackage =>
      "A1A22_OBSTRUCTION_NO_REMAINING_NON_GRAPH_EVIDENCE_PACKAGE"
  | .noFiniteEndpointFluxClosure =>
      "A1A22_OBSTRUCTION_NO_FINITE_ENDPOINT_FLUX_CLOSURE"
  | .noFiniteRawIBPGreenIdentityClosure =>
      "A1A22_OBSTRUCTION_NO_FINITE_RAW_IBP_GREEN_IDENTITY_CLOSURE"
  | .noFinitePairingConvergence =>
      "A1A22_OBSTRUCTION_NO_FINITE_PAIRING_CONVERGENCE"
  | .noTraceNormalDerivativeConvergence =>
      "A1A22_OBSTRUCTION_NO_TRACE_NORMAL_DERIVATIVE_CONVERGENCE"
  | .noDomainRegularityForLimitPassage =>
      "A1A22_OBSTRUCTION_NO_DOMAIN_REGULARITY_FOR_LIMIT_PASSAGE"
  | .noOrientationCompatibility =>
      "A1A22_OBSTRUCTION_NO_ORIENTATION_COMPATIBILITY"
  | .noSeparatingTestClassForLimit =>
      "A1A22_OBSTRUCTION_NO_SEPARATING_TEST_CLASS_FOR_LIMIT"
  | .noTargetContinuumSemanticsPackage =>
      "A1A22_OBSTRUCTION_NO_TARGET_CONTINUUM_SEMANTICS_PACKAGE"
  | .noA2A15BoundaryFluxClosure =>
      "A1A22_OBSTRUCTION_NO_A2A15_BOUNDARY_FLUX_CLOSURE"
  | .noPhase2Authorization =>
      "A1A22_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A22 specialized witness attempt. -/
def specializedA2A15A1WitnessObstructionsV0 :
    List SpecializedA2A15A1WitnessObstruction :=
  [ .noRemainingNonGraphEvidencePackage
  , .noFiniteEndpointFluxClosure
  , .noFiniteRawIBPGreenIdentityClosure
  , .noFinitePairingConvergence
  , .noTraceNormalDerivativeConvergence
  , .noDomainRegularityForLimitPassage
  , .noOrientationCompatibility
  , .noSeparatingTestClassForLimit
  , .noTargetContinuumSemanticsPackage
  , .noA2A15BoundaryFluxClosure
  , .noPhase2Authorization
  ]

/-- The A1A22 obstruction list is stable and explicit. -/
theorem specialized_a2a15a1_witness_obstructions_v0_expected :
    specializedA2A15A1WitnessObstructionsV0 =
      [ .noRemainingNonGraphEvidencePackage
      , .noFiniteEndpointFluxClosure
      , .noFiniteRawIBPGreenIdentityClosure
      , .noFinitePairingConvergence
      , .noTraceNormalDerivativeConvergence
      , .noDomainRegularityForLimitPassage
      , .noOrientationCompatibility
      , .noSeparatingTestClassForLimit
      , .noTargetContinuumSemanticsPackage
      , .noA2A15BoundaryFluxClosure
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A22 proves a conditional witness and records a concrete obstruction. -/
def specializedA2A15A1WitnessSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A22 successor kind is stable and explicit. -/
theorem specialized_a2a15a1_witness_successor_kinds_v0_expected :
    specializedA2A15A1WitnessSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A22 specialized A2A15A1 witness attempt. -/
structure SpecializedA2A15A1WitnessStatus where
  specialized_graph_field_filled : Prop
  specialized_graph_field_filled_supplied :
    specialized_graph_field_filled
  conditional_specialized_witness_constructor_defined : Prop
  conditional_specialized_witness_constructor_defined_supplied :
    conditional_specialized_witness_constructor_defined
  graph_slot_no_longer_witness_blocker : Prop
  graph_slot_no_longer_witness_blocker_supplied :
    graph_slot_no_longer_witness_blocker
  evidence_free_witness_refuted : Prop
  evidence_free_witness_refuted_supplied :
    evidence_free_witness_refuted
  remaining_non_graph_evidence_supplied : Prop
  remaining_non_graph_evidence_not_supplied :
    Not remaining_non_graph_evidence_supplied
  a2a15a1_closed : Prop
  a2a15a1_not_closed : Not a2a15a1_closed
  a2a15_boundary_flux_parent_closed : Prop
  a2a15_boundary_flux_parent_not_closed :
    Not a2a15_boundary_flux_parent_closed
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
Current A1A22 result: the graph slot can be filled inside the specialized
legacy view, and a full A2A15A1 witness is constructed conditionally on the
remaining non-graph evidence.  That remaining evidence is not supplied here.
-/
def specializedA2A15A1WitnessStatusV0 :
    SpecializedA2A15A1WitnessStatus where
  specialized_graph_field_filled := True
  specialized_graph_field_filled_supplied := True.intro
  conditional_specialized_witness_constructor_defined := True
  conditional_specialized_witness_constructor_defined_supplied := True.intro
  graph_slot_no_longer_witness_blocker := True
  graph_slot_no_longer_witness_blocker_supplied := True.intro
  evidence_free_witness_refuted := True
  evidence_free_witness_refuted_supplied := True.intro
  remaining_non_graph_evidence_supplied := False
  remaining_non_graph_evidence_not_supplied := by
    intro h
    exact h
  a2a15a1_closed := False
  a2a15a1_not_closed := by
    intro h
    exact h
  a2a15_boundary_flux_parent_closed := False
  a2a15_boundary_flux_parent_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  surface_id := a1a22SpecializedA2A15A1WitnessSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A21ParentGraphChannelInterfaceRefactorRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A22SpecializedA2A15A1WitnessRetainedId
  outcome_id := specializedA2A15A1WitnessRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := specializedA2A15A1WitnessSuccessorKindsV0
  obstruction_ids :=
    specializedA2A15A1WitnessObstructionsV0.map
      specializedA2A15A1WitnessObstructionId

/-- Short proof-facing status alias. -/
def specializedA2A15A1WitnessStatusReadoutV0 :
    SpecializedA2A15A1WitnessStatus :=
  specializedA2A15A1WitnessStatusV0

/-- The specialized graph field is filled by A1A16/A1A21. -/
theorem specialized_a2a15a1_witness_graph_field_filled_v0 :
    specializedA2A15A1WitnessStatusReadoutV0
      |>.specialized_graph_field_filled := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.specialized_graph_field_filled_supplied

/-- The conditional specialized witness constructor is defined. -/
theorem specialized_a2a15a1_witness_constructor_defined_v0 :
    specializedA2A15A1WitnessStatusReadoutV0
      |>.conditional_specialized_witness_constructor_defined := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.conditional_specialized_witness_constructor_defined_supplied

/-- The graph slot is no longer the specialized-witness blocker. -/
theorem specialized_a2a15a1_witness_graph_slot_no_longer_blocker_v0 :
    specializedA2A15A1WitnessStatusReadoutV0
      |>.graph_slot_no_longer_witness_blocker := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.graph_slot_no_longer_witness_blocker_supplied

/-- Evidence-free specialized A2A15A1 witness construction is refuted. -/
theorem specialized_a2a15a1_witness_evidence_free_refuted_v0 :
    specializedA2A15A1WitnessStatusReadoutV0
      |>.evidence_free_witness_refuted := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.evidence_free_witness_refuted_supplied

/-- The remaining non-graph evidence is not supplied by A1A22. -/
theorem specialized_a2a15a1_witness_remaining_evidence_not_supplied_v0 :
    Not
      (specializedA2A15A1WitnessStatusReadoutV0
        |>.remaining_non_graph_evidence_supplied) := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.remaining_non_graph_evidence_not_supplied

/-- A2A15A1 is still not closed by A1A22. -/
theorem specialized_a2a15a1_witness_a2a15a1_not_closed_v0 :
    Not (specializedA2A15A1WitnessStatusReadoutV0 |>.a2a15a1_closed) := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.a2a15a1_not_closed

/-- A2A15 remains not closed by A1A22. -/
theorem specialized_a2a15a1_witness_a2a15_not_closed_v0 :
    Not
      (specializedA2A15A1WitnessStatusReadoutV0
        |>.a2a15_boundary_flux_parent_closed) := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.a2a15_boundary_flux_parent_not_closed

/-- Phase 2 remains unauthorized after A1A22. -/
theorem specialized_a2a15a1_witness_phase2_not_authorized_v0 :
    Not (specializedA2A15A1WitnessStatusReadoutV0 |>.phase2Authorized) := by
  exact
    specializedA2A15A1WitnessStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A22 retained blocker id is exposed. -/
theorem specialized_a2a15a1_witness_retained_id_v0 :
    specializedA2A15A1WitnessStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A22SpecializedA2A15A1WitnessRetainedId := by
  rfl

/-- The A1A22 outcome id is exposed. -/
theorem specialized_a2a15a1_witness_outcome_id_v0 :
    specializedA2A15A1WitnessStatusReadoutV0.outcome_id =
      specializedA2A15A1WitnessRetainedOutcomeId := by
  rfl

/-- The A1A22 obstruction ids are exposed. -/
theorem specialized_a2a15a1_witness_obstruction_ids_v0 :
    specializedA2A15A1WitnessStatusReadoutV0.obstruction_ids =
      specializedA2A15A1WitnessObstructionsV0.map
        specializedA2A15A1WitnessObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness
end QFT
end ToeFormal
