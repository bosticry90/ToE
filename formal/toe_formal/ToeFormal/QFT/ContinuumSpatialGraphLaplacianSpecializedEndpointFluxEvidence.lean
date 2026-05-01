/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence.lean

A1A23 endpoint-flux split for the specialized A2A15A1 witness route.

Scope:
- isolate the non-endpoint fields that remain after the A2A15A1B
  endpoint-flux channel is supplied
- prove supplied endpoint-flux channel evidence fills the specialized
  endpoint-flux, trace-normal, boundary-trace, and orientation fields
- assemble the A1A22 remaining-evidence package from endpoint evidence plus
  the still-independent non-endpoint obligations
- retain endpoint-flux derivation, A2A15A1 closure, A2A15 closure, and
  Phase 2 authorization
- make no Phase 0-5 objective-completion claim
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialRawIBPProofContract
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialEndpointFluxConvergence
open ContinuumSpatialGraphLaplacianParentInterfaceMapFromActualGraphError
open ContinuumSpatialGraphLaplacianParentGraphChannelInterfaceRefactor
open ContinuumSpatialGraphLaplacianSpecializedA2A15A1Witness

set_option autoImplicit false

noncomputable section

/-- Surface id for the A1A23 specialized endpoint-flux evidence split. -/
def a1a23SpecializedEndpointFluxEvidenceSurfaceId : String :=
  "A2A15A1A23_SPECIALIZED_ENDPOINT_FLUX_EVIDENCE"

/-- Retained blocker after the specialized endpoint-flux evidence split. -/
def phase1Blocker003A2A15A1A23SpecializedEndpointFluxEvidenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A23_SPECIALIZED_ENDPOINT_FLUX_" ++
    "EVIDENCE_RETAINED"

/-- Outcome id for the retained A1A23 endpoint-flux evidence slice. -/
def specializedEndpointFluxEvidenceRetainedOutcomeId : String :=
  "SPECIALIZED_ENDPOINT_FLUX_EVIDENCE_RETAINED"

/--
The A1A22 fields that remain after endpoint-flux channel evidence is supplied.

Endpoint evidence supplies the parent boundary trace/normal semantics, target
orientation, endpoint-flux convergence, trace-normal convergence, and
orientation compatibility.  The fields below remain independent obligations.
-/
structure SpecializedA2A15A1NonEndpointRemainingEvidence
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
  target_domain_regular_for_limit_passage_supplied :
    target.domain_regular_for_limit_passage
  finite_raw_ibp_green_identity_convergence_supplied :
    contract.finite_raw_ibp_to_continuum_green_identity
  finite_pairing_convergence_supplied :
    contract.finite_pairing_to_continuum_pairing
  contract_domain_regular_for_limit_passage_supplied :
    contract.domain_regular_for_limit_passage
  separating_test_class_for_limit_supplied :
    contract.separating_test_class_for_limit

/-- Supplied endpoint-flux evidence fills the specialized endpoint field. -/
theorem specialized_endpoint_flux_evidence_supplies_endpoint_field_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract)) :
    contract.finite_endpoint_flux_to_continuum_boundary_flux := by
  exact endpoint_flux_channel_supplies_parent_contract_field endpointEvidence

/-- Supplied endpoint-flux evidence fills boundary trace/normal semantics. -/
theorem specialized_endpoint_flux_evidence_supplies_boundary_trace_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract)) :
    target.boundary_trace_normal_derivative_semantics := by
  exact
    endpoint_flux_channel_supplies_parent_boundary_trace_normal_derivative
      endpointEvidence

/-- Supplied endpoint-flux evidence fills target orientation semantics. -/
theorem specialized_endpoint_flux_evidence_supplies_orientation_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract)) :
    target.orientation_convention_for_limit := by
  exact endpoint_flux_channel_supplies_parent_orientation endpointEvidence

/-- Supplied endpoint-flux evidence fills trace-normal convergence. -/
theorem specialized_endpoint_flux_evidence_supplies_trace_normal_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract)) :
    contract.trace_normal_derivative_convergence := by
  exact endpoint_flux_channel_supplies_parent_trace_normal_convergence
    endpointEvidence

/-- Supplied endpoint-flux evidence fills orientation compatibility. -/
theorem specialized_endpoint_flux_evidence_supplies_orientation_compatibility_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract)) :
    contract.orientation_convention_compatible := by
  exact
    endpoint_flux_channel_supplies_parent_orientation_compatibility
      endpointEvidence

/--
Endpoint evidence plus non-endpoint remaining evidence gives the full A1A22
remaining-evidence package.
-/
def specializedRemainingEvidenceOfEndpointFluxEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract))
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    SpecializedA2A15A1RemainingEvidence contract where
  analytic_interval_domain_model_supplied :=
    remaining.analytic_interval_domain_model_supplied
  continuum_derivative_laplacian_semantics_supplied :=
    remaining.continuum_derivative_laplacian_semantics_supplied
  boundary_trace_normal_derivative_semantics_supplied :=
    specialized_endpoint_flux_evidence_supplies_boundary_trace_v0
      contract endpointEvidence
  target_domain_regular_for_limit_passage_supplied :=
    remaining.target_domain_regular_for_limit_passage_supplied
  target_orientation_convention_for_limit_supplied :=
    specialized_endpoint_flux_evidence_supplies_orientation_v0
      contract endpointEvidence
  finite_endpoint_flux_convergence_supplied :=
    specialized_endpoint_flux_evidence_supplies_endpoint_field_v0
      contract endpointEvidence
  finite_raw_ibp_green_identity_convergence_supplied :=
    remaining.finite_raw_ibp_green_identity_convergence_supplied
  finite_pairing_convergence_supplied :=
    remaining.finite_pairing_convergence_supplied
  trace_normal_derivative_convergence_supplied :=
    specialized_endpoint_flux_evidence_supplies_trace_normal_v0
      contract endpointEvidence
  contract_domain_regular_for_limit_passage_supplied :=
    remaining.contract_domain_regular_for_limit_passage_supplied
  orientation_convention_compatible_supplied :=
    specialized_endpoint_flux_evidence_supplies_orientation_compatibility_v0
      contract endpointEvidence
  separating_test_class_for_limit_supplied :=
    remaining.separating_test_class_for_limit_supplied

/--
Conditional specialized A2A15A1 witness after the endpoint-flux split.

This is still conditional: endpoint evidence is supplied by the caller, and
the non-endpoint fields remain independent obligations.
-/
def specializedA2A15A1WitnessOfEndpointFluxEvidence
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract))
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    AnalyticIntervalLiftWitness
      target
      (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        contract) :=
  specializedA2A15A1WitnessOfRemainingEvidence
    contract
    (specializedRemainingEvidenceOfEndpointFluxEvidence
      contract endpointEvidence remaining)

/-- The endpoint-split conditional witness supplies raw spatial IBP. -/
theorem specialized_endpoint_flux_witness_supplies_raw_ibp_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract))
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    RawSpatialIntegrationByPartsStatement
      target.continuum_problem
      target.continuum_raw_boundary_flux := by
  exact
    specialized_a2a15a1_witness_supplies_raw_ibp_v0
      contract
      (specializedRemainingEvidenceOfEndpointFluxEvidence
        contract endpointEvidence remaining)

/-- The endpoint-split conditional witness feeds the A2A14 route. -/
theorem specialized_endpoint_flux_witness_feeds_a2a14_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (contract :
      ActualErrorSpecializedParentGraphChannelContract
        (f := f) target x C)
    (endpointEvidence :
      FiniteEndpointFluxToContinuumBoundaryFluxChannelEvidence
        target
        (analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
          contract))
    (remaining :
      SpecializedA2A15A1NonEndpointRemainingEvidence contract) :
    SpatialLaplacianGreenIdentityStatement target.continuum_problem := by
  exact
    specialized_a2a15a1_witness_feeds_a2a14_v0
      contract
      (specializedRemainingEvidenceOfEndpointFluxEvidence
        contract endpointEvidence remaining)

/--
Graph evidence alone still cannot derive the endpoint-flux slot: a legal
specialized contract can set that slot to `False`.
-/
theorem specialized_endpoint_flux_field_evidence_free_refuted_v0
    {ContinuumPoint : Type}
    {target : AnalyticIntervalLiftTarget ContinuumPoint}
    {f : Real -> Real}
    {x C : Real}
    (evidenceOnly : ActualGraphErrorEvidenceOnly (f := f) x C) :
    Not
      ((analyticIntervalLiftConvergenceContractOfSpecializedGraphChannel
        (specializedParentContractWithFalseEndpointFlux
          (target := target) evidenceOnly))
        |>.finite_endpoint_flux_to_continuum_boundary_flux) := by
  intro h
  exact h

/-- Remaining objects after the A1A23 endpoint-flux evidence split. -/
inductive SpecializedEndpointFluxEvidenceObstruction where
  | noEndpointFluxEvidencePackage
  | noEndpointFluxRepresentation
  | noContinuumBoundaryTraceSemantics
  | noContinuumNormalDerivativeSemantics
  | noBoundaryReconstructionCompatibility
  | noFluxTermConvergenceMode
  | noFiniteEndpointFluxConsistencyTheorem
  | noTraceNormalDerivativeConvergence
  | noOrientationCompatibility
  | noRemainingNonEndpointA2A15A1Evidence
  | noA2A15A1Closure
  | noA2A15BoundaryFluxClosure
  | noPhase2Authorization
deriving DecidableEq, Repr

/-- Machine-facing ids for retained A1A23 objects. -/
def specializedEndpointFluxEvidenceObstructionId :
    SpecializedEndpointFluxEvidenceObstruction -> String
  | .noEndpointFluxEvidencePackage =>
      "A1A23_OBSTRUCTION_NO_ENDPOINT_FLUX_EVIDENCE_PACKAGE"
  | .noEndpointFluxRepresentation =>
      "A1A23_OBSTRUCTION_NO_ENDPOINT_FLUX_REPRESENTATION"
  | .noContinuumBoundaryTraceSemantics =>
      "A1A23_OBSTRUCTION_NO_CONTINUUM_BOUNDARY_TRACE_SEMANTICS"
  | .noContinuumNormalDerivativeSemantics =>
      "A1A23_OBSTRUCTION_NO_CONTINUUM_NORMAL_DERIVATIVE_SEMANTICS"
  | .noBoundaryReconstructionCompatibility =>
      "A1A23_OBSTRUCTION_NO_BOUNDARY_RECONSTRUCTION_COMPATIBILITY"
  | .noFluxTermConvergenceMode =>
      "A1A23_OBSTRUCTION_NO_FLUX_TERM_CONVERGENCE_MODE"
  | .noFiniteEndpointFluxConsistencyTheorem =>
      "A1A23_OBSTRUCTION_NO_FINITE_ENDPOINT_FLUX_CONSISTENCY_THEOREM"
  | .noTraceNormalDerivativeConvergence =>
      "A1A23_OBSTRUCTION_NO_TRACE_NORMAL_DERIVATIVE_CONVERGENCE"
  | .noOrientationCompatibility =>
      "A1A23_OBSTRUCTION_NO_ORIENTATION_COMPATIBILITY"
  | .noRemainingNonEndpointA2A15A1Evidence =>
      "A1A23_OBSTRUCTION_NO_REMAINING_NON_ENDPOINT_A2A15A1_EVIDENCE"
  | .noA2A15A1Closure =>
      "A1A23_OBSTRUCTION_NO_A2A15A1_CLOSURE"
  | .noA2A15BoundaryFluxClosure =>
      "A1A23_OBSTRUCTION_NO_A2A15_BOUNDARY_FLUX_CLOSURE"
  | .noPhase2Authorization =>
      "A1A23_OBSTRUCTION_NO_PHASE2_AUTHORIZATION"

/-- Exact obstruction list after the A1A23 endpoint-flux split. -/
def specializedEndpointFluxEvidenceObstructionsV0 :
    List SpecializedEndpointFluxEvidenceObstruction :=
  [ .noEndpointFluxEvidencePackage
  , .noEndpointFluxRepresentation
  , .noContinuumBoundaryTraceSemantics
  , .noContinuumNormalDerivativeSemantics
  , .noBoundaryReconstructionCompatibility
  , .noFluxTermConvergenceMode
  , .noFiniteEndpointFluxConsistencyTheorem
  , .noTraceNormalDerivativeConvergence
  , .noOrientationCompatibility
  , .noRemainingNonEndpointA2A15A1Evidence
  , .noA2A15A1Closure
  , .noA2A15BoundaryFluxClosure
  , .noPhase2Authorization
  ]

/-- The A1A23 obstruction list is stable and explicit. -/
theorem specialized_endpoint_flux_evidence_obstructions_v0_expected :
    specializedEndpointFluxEvidenceObstructionsV0 =
      [ .noEndpointFluxEvidencePackage
      , .noEndpointFluxRepresentation
      , .noContinuumBoundaryTraceSemantics
      , .noContinuumNormalDerivativeSemantics
      , .noBoundaryReconstructionCompatibility
      , .noFluxTermConvergenceMode
      , .noFiniteEndpointFluxConsistencyTheorem
      , .noTraceNormalDerivativeConvergence
      , .noOrientationCompatibility
      , .noRemainingNonEndpointA2A15A1Evidence
      , .noA2A15A1Closure
      , .noA2A15BoundaryFluxClosure
      , .noPhase2Authorization
      ] := by
  rfl

/-- A1A23 proves a conditional connector and records concrete obstruction. -/
def specializedEndpointFluxEvidenceSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .provesChannel, .recordsConcreteObstruction ]

/-- The A1A23 successor kind is stable and explicit. -/
theorem specialized_endpoint_flux_evidence_successor_kinds_v0_expected :
    specializedEndpointFluxEvidenceSuccessorKindsV0 =
      [ .provesChannel, .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the A1A23 endpoint-flux evidence split. -/
structure SpecializedEndpointFluxEvidenceStatus where
  endpoint_flux_evidence_connector_defined : Prop
  endpoint_flux_evidence_connector_defined_supplied :
    endpoint_flux_evidence_connector_defined
  supplied_endpoint_evidence_fills_endpoint_field : Prop
  supplied_endpoint_evidence_fills_endpoint_field_supplied :
    supplied_endpoint_evidence_fills_endpoint_field
  supplied_endpoint_evidence_fills_trace_orientation_fields : Prop
  supplied_endpoint_evidence_fills_trace_orientation_fields_supplied :
    supplied_endpoint_evidence_fills_trace_orientation_fields
  conditional_remaining_evidence_constructor_defined : Prop
  conditional_remaining_evidence_constructor_defined_supplied :
    conditional_remaining_evidence_constructor_defined
  evidence_free_endpoint_field_refuted : Prop
  evidence_free_endpoint_field_refuted_supplied :
    evidence_free_endpoint_field_refuted
  endpoint_flux_evidence_supplied : Prop
  endpoint_flux_evidence_not_supplied :
    Not endpoint_flux_evidence_supplied
  remaining_non_endpoint_evidence_supplied : Prop
  remaining_non_endpoint_evidence_not_supplied :
    Not remaining_non_endpoint_evidence_supplied
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
Current A1A23 result: endpoint-flux evidence has an exact connector into the
specialized A1A22 witness package, but the endpoint evidence itself and the
remaining non-endpoint evidence are not derived here.
-/
def specializedEndpointFluxEvidenceStatusV0 :
    SpecializedEndpointFluxEvidenceStatus where
  endpoint_flux_evidence_connector_defined := True
  endpoint_flux_evidence_connector_defined_supplied := True.intro
  supplied_endpoint_evidence_fills_endpoint_field := True
  supplied_endpoint_evidence_fills_endpoint_field_supplied := True.intro
  supplied_endpoint_evidence_fills_trace_orientation_fields := True
  supplied_endpoint_evidence_fills_trace_orientation_fields_supplied :=
    True.intro
  conditional_remaining_evidence_constructor_defined := True
  conditional_remaining_evidence_constructor_defined_supplied := True.intro
  evidence_free_endpoint_field_refuted := True
  evidence_free_endpoint_field_refuted_supplied := True.intro
  endpoint_flux_evidence_supplied := False
  endpoint_flux_evidence_not_supplied := by
    intro h
    exact h
  remaining_non_endpoint_evidence_supplied := False
  remaining_non_endpoint_evidence_not_supplied := by
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
  surface_id := a1a23SpecializedEndpointFluxEvidenceSurfaceId
  prior_retained_blocker_id :=
    phase1Blocker003A2A15A1A22SpecializedA2A15A1WitnessRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A23SpecializedEndpointFluxEvidenceRetainedId
  outcome_id := specializedEndpointFluxEvidenceRetainedOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := specializedEndpointFluxEvidenceSuccessorKindsV0
  obstruction_ids :=
    specializedEndpointFluxEvidenceObstructionsV0.map
      specializedEndpointFluxEvidenceObstructionId

/-- Short proof-facing status alias. -/
def specializedEndpointFluxEvidenceStatusReadoutV0 :
    SpecializedEndpointFluxEvidenceStatus :=
  specializedEndpointFluxEvidenceStatusV0

/-- The endpoint-flux connector is defined. -/
theorem specialized_endpoint_flux_evidence_connector_defined_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.endpoint_flux_evidence_connector_defined := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.endpoint_flux_evidence_connector_defined_supplied

/-- Supplied endpoint evidence fills the specialized endpoint field. -/
theorem specialized_endpoint_flux_evidence_fills_endpoint_status_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.supplied_endpoint_evidence_fills_endpoint_field := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.supplied_endpoint_evidence_fills_endpoint_field_supplied

/-- Supplied endpoint evidence fills trace/orientation fields. -/
theorem specialized_endpoint_flux_evidence_fills_trace_orientation_status_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.supplied_endpoint_evidence_fills_trace_orientation_fields := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.supplied_endpoint_evidence_fills_trace_orientation_fields_supplied

/-- The conditional remaining-evidence constructor is defined. -/
theorem specialized_endpoint_flux_remaining_constructor_defined_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.conditional_remaining_evidence_constructor_defined := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.conditional_remaining_evidence_constructor_defined_supplied

/-- Evidence-free endpoint-field derivation is refuted. -/
theorem specialized_endpoint_flux_evidence_free_refuted_status_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.evidence_free_endpoint_field_refuted := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.evidence_free_endpoint_field_refuted_supplied

/-- Endpoint-flux evidence is not supplied by A1A23. -/
theorem specialized_endpoint_flux_evidence_not_supplied_v0 :
    Not
      (specializedEndpointFluxEvidenceStatusReadoutV0
        |>.endpoint_flux_evidence_supplied) := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.endpoint_flux_evidence_not_supplied

/-- Non-endpoint remaining evidence is not supplied by A1A23. -/
theorem specialized_endpoint_flux_non_endpoint_evidence_not_supplied_v0 :
    Not
      (specializedEndpointFluxEvidenceStatusReadoutV0
        |>.remaining_non_endpoint_evidence_supplied) := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.remaining_non_endpoint_evidence_not_supplied

/-- A2A15A1 is still not closed by A1A23. -/
theorem specialized_endpoint_flux_evidence_a2a15a1_not_closed_v0 :
    Not
      (specializedEndpointFluxEvidenceStatusReadoutV0 |>.a2a15a1_closed) := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.a2a15a1_not_closed

/-- A2A15 remains not closed by A1A23. -/
theorem specialized_endpoint_flux_evidence_a2a15_not_closed_v0 :
    Not
      (specializedEndpointFluxEvidenceStatusReadoutV0
        |>.a2a15_boundary_flux_parent_closed) := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.a2a15_boundary_flux_parent_not_closed

/-- Phase 2 remains unauthorized after A1A23. -/
theorem specialized_endpoint_flux_evidence_phase2_not_authorized_v0 :
    Not
      (specializedEndpointFluxEvidenceStatusReadoutV0
        |>.phase2Authorized) := by
  exact
    specializedEndpointFluxEvidenceStatusReadoutV0
      |>.phase2_not_authorized

/-- The A1A23 retained blocker id is exposed. -/
theorem specialized_endpoint_flux_evidence_retained_id_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A23SpecializedEndpointFluxEvidenceRetainedId := by
  rfl

/-- The A1A23 outcome id is exposed. -/
theorem specialized_endpoint_flux_evidence_outcome_id_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0.outcome_id =
      specializedEndpointFluxEvidenceRetainedOutcomeId := by
  rfl

/-- The A1A23 obstruction ids are exposed. -/
theorem specialized_endpoint_flux_evidence_obstruction_ids_v0 :
    specializedEndpointFluxEvidenceStatusReadoutV0.obstruction_ids =
      specializedEndpointFluxEvidenceObstructionsV0.map
        specializedEndpointFluxEvidenceObstructionId := by
  rfl

end

end ContinuumSpatialGraphLaplacianSpecializedEndpointFluxEvidence
end QFT
end ToeFormal
