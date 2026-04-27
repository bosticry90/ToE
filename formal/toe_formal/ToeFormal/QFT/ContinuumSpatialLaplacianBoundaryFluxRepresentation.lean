/-
ToeFormal/QFT/ContinuumSpatialLaplacianBoundaryFluxRepresentation.lean

Spatial Laplacian boundary-flux representation surface for
PHASE1-BLOCKER-003A2A15.

Scope:
- isolate the boundary-flux representation dependency inside the A2A14
  spatial Green-identity obligation
- state a raw spatial integration-by-parts boundary term and the theorem that
  represents it by the existing two-sided boundary flux model
- prove that supplied raw integration-by-parts and representation evidence
  give the A2A14 spatial Green identity
- keep concrete spatial integration theory, trace/normal-derivative semantics,
  boundary orientation derivation, concrete Laplacian construction, separating
  test class, full-field route recovery, and Phase 2 authorization out of scope
-/

import ToeFormal.QFT.ContinuumSpatialLaplacianGreenIdentityObligation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialLaplacianBoundaryFluxRepresentation

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumResidualAdmissibility
open ContinuumNonzeroScalarKineticOperatorDomainClosure
open ContinuumTrueScalarKineticOperatorCandidate
open ContinuumSpatialLaplacianKineticCandidate
open ContinuumSpatialLaplacianGreenIdentityObligation

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the spatial boundary-flux representation slice. -/
def phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15_SPATIAL_LAPLACIAN_BOUNDARY_FLUX_" ++
    "REPRESENTATION_RETAINED"

/-- Outcome id for this bounded boundary-flux representation surface. -/
def spatialBoundaryFluxRepresentationOutcomeId : String :=
  "SPATIAL_LAPLACIAN_BOUNDARY_FLUX_REPRESENTATION_RECORDED_" ++
    "GREEN_IDENTITY_RETAINED"

/-- Missing objects after the boundary-flux representation surface. -/
inductive Phase1Blocker003A2A15MissingObject where
  | concreteSpatialBoundaryTermDerivation
  | traceNormalDerivativeSemantics
  | rawBoundaryTermToTwoSidedFluxTheorem
  | domainRegularityForBoundaryEvaluation
  | orientationSignConvention
  | concreteSpatialIntegrationByParts
  | concreteSpatialLaplacianConstruction
  | concreteSeparatingTestClass
  | fullFieldContinuumRouteRecovery
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A15 objects. -/
def phase1Blocker003A2A15MissingObjectId :
    Phase1Blocker003A2A15MissingObject -> String
  | .concreteSpatialBoundaryTermDerivation =>
      "003A2A15_CONCRETE_SPATIAL_BOUNDARY_TERM_DERIVATION_RETAINED"
  | .traceNormalDerivativeSemantics =>
      "003A2A15_TRACE_NORMAL_DERIVATIVE_SEMANTICS_RETAINED"
  | .rawBoundaryTermToTwoSidedFluxTheorem =>
      "003A2A15_RAW_BOUNDARY_TERM_TO_TWO_SIDED_FLUX_RETAINED"
  | .domainRegularityForBoundaryEvaluation =>
      "003A2A15_DOMAIN_REGULARITY_FOR_BOUNDARY_EVALUATION_RETAINED"
  | .orientationSignConvention =>
      "003A2A15_ORIENTATION_SIGN_CONVENTION_RETAINED"
  | .concreteSpatialIntegrationByParts =>
      "003A2A15_CONCRETE_SPATIAL_INTEGRATION_BY_PARTS_RETAINED"
  | .concreteSpatialLaplacianConstruction =>
      "003A2A15_CONCRETE_SPATIAL_LAPLACIAN_CONSTRUCTION_RETAINED"
  | .concreteSeparatingTestClass =>
      "003A2A15_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"
  | .fullFieldContinuumRouteRecovery =>
      "003A2A15_FULL_FIELD_CONTINUUM_ROUTE_RECOVERY_RETAINED"

/-- The explicit remaining objects after this bounded surface. -/
def phase1Blocker003A2A15MissingObjectsV0 :
    List Phase1Blocker003A2A15MissingObject :=
  [ .concreteSpatialBoundaryTermDerivation
  , .traceNormalDerivativeSemantics
  , .rawBoundaryTermToTwoSidedFluxTheorem
  , .domainRegularityForBoundaryEvaluation
  , .orientationSignConvention
  , .concreteSpatialIntegrationByParts
  , .concreteSpatialLaplacianConstruction
  , .concreteSeparatingTestClass
  , .fullFieldContinuumRouteRecovery
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a15_missing_objects_v0_expected :
    phase1Blocker003A2A15MissingObjectsV0 =
      [ .concreteSpatialBoundaryTermDerivation
      , .traceNormalDerivativeSemantics
      , .rawBoundaryTermToTwoSidedFluxTheorem
      , .domainRegularityForBoundaryEvaluation
      , .orientationSignConvention
      , .concreteSpatialIntegrationByParts
      , .concreteSpatialLaplacianConstruction
      , .concreteSeparatingTestClass
      , .fullFieldContinuumRouteRecovery
      ] := by
  rfl

/-- Abstract raw boundary flux produced by a spatial integration-by-parts law. -/
abbrev RawSpatialBoundaryFlux (Point : Type) :=
  ContinuumField Point -> ContinuumField Point -> Real

/--
Raw integration-by-parts statement before identifying the boundary term with
the repository's two-sided boundary flux.
-/
def RawSpatialIntegrationByPartsStatement {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (rawBoundaryFlux : RawSpatialBoundaryFlux Point) : Prop :=
  forall x y : ContinuumField Point,
    problem.InOperatorDomain x ->
    problem.InOperatorDomain y ->
      ContinuumPair problem.integral x (problem.kineticOperator y) =
        ContinuumPair problem.integral y (problem.kineticOperator x) +
          rawBoundaryFlux x y

/--
Boundary-flux representation statement: the raw boundary term from spatial
integration by parts is the existing two-sided boundary flux.
-/
def BoundaryFluxRepresentationStatement {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (rawBoundaryFlux : RawSpatialBoundaryFlux Point) : Prop :=
  forall x y : ContinuumField Point,
    problem.InOperatorDomain x ->
    problem.InOperatorDomain y ->
      rawBoundaryFlux x y = twoSidedBoundaryFlux problem.trace x y

/--
Evidence package for reducing the spatial Green identity to a boundary-flux
representation theorem.

This is still conditional analytic evidence: it records the raw
integration-by-parts theorem and the theorem that rewrites its boundary term
as the repo-native two-sided flux.
-/
structure SpatialLaplacianBoundaryFluxRepresentation {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  selected_problem : ScalarKineticBoundaryProblemSelected problem
  spatial_laplacian_operator_selected : Prop
  spatial_laplacian_operator_selected_supplied :
    spatial_laplacian_operator_selected
  raw_boundary_flux : RawSpatialBoundaryFlux Point
  concrete_spatial_integration_by_parts_source : Prop
  concrete_spatial_integration_by_parts_source_supplied :
    concrete_spatial_integration_by_parts_source
  spatial_boundary_trace_theorem : Prop
  spatial_boundary_trace_theorem_supplied :
    spatial_boundary_trace_theorem
  spatial_laplacian_domain_regular : Prop
  spatial_laplacian_domain_regular_supplied :
    spatial_laplacian_domain_regular
  trace_normal_derivative_semantics : Prop
  trace_normal_derivative_semantics_supplied :
    trace_normal_derivative_semantics
  boundary_orientation_sign_convention : Prop
  boundary_orientation_sign_convention_supplied :
    boundary_orientation_sign_convention
  raw_integration_by_parts :
    RawSpatialIntegrationByPartsStatement problem raw_boundary_flux
  boundary_flux_representation :
    BoundaryFluxRepresentationStatement problem raw_boundary_flux

/--
Raw integration by parts plus boundary-flux representation gives the spatial
Green-identity statement required by A2A14.
-/
theorem spatial_green_identity_statement_of_boundary_flux_representation
    {Point : Type}
    {problem : ScalarKineticBoundaryProblem Point}
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    SpatialLaplacianGreenIdentityStatement problem := by
  intro x y hx hy
  calc
    ContinuumPair problem.integral x (problem.kineticOperator y) =
        ContinuumPair problem.integral y (problem.kineticOperator x) +
          representation.raw_boundary_flux x y :=
      representation.raw_integration_by_parts x y hx hy
    _ = ContinuumPair problem.integral y (problem.kineticOperator x) +
          twoSidedBoundaryFlux problem.trace x y := by
      rw [representation.boundary_flux_representation x y hx hy]

/-- Boundary-flux representation evidence supplies the A2A14 obligation. -/
def spatialGreenIdentityObligationOfBoundaryFluxRepresentation
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    SpatialLaplacianGreenIdentityObligation problem where
  selected_problem := representation.selected_problem
  spatial_laplacian_operator_selected :=
    representation.spatial_laplacian_operator_selected
  spatial_laplacian_operator_selected_supplied :=
    representation.spatial_laplacian_operator_selected_supplied
  concrete_spatial_integration_by_parts_source :=
    representation.concrete_spatial_integration_by_parts_source
  concrete_spatial_integration_by_parts_source_supplied :=
    representation.concrete_spatial_integration_by_parts_source_supplied
  spatial_boundary_trace_theorem :=
    representation.spatial_boundary_trace_theorem
  spatial_boundary_trace_theorem_supplied :=
    representation.spatial_boundary_trace_theorem_supplied
  spatial_laplacian_domain_regular :=
    representation.spatial_laplacian_domain_regular
  spatial_laplacian_domain_regular_supplied :=
    representation.spatial_laplacian_domain_regular_supplied
  boundary_flux_represents_trace_terms :=
    BoundaryFluxRepresentationStatement
      problem representation.raw_boundary_flux
  boundary_flux_represents_trace_terms_supplied :=
    representation.boundary_flux_representation
  green_identity_statement :=
    spatial_green_identity_statement_of_boundary_flux_representation
      representation

/-- Boundary-flux representation evidence feeds A2A13. -/
def spatialLaplacianCandidateOfBoundaryFluxRepresentation
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (base :
      SpatialLaplacianCandidateWithoutGreenIdentity
        problem massSq FieldClass)
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    SpatialLaplacianKineticCandidate problem massSq FieldClass :=
  spatialLaplacianCandidateOfGreenIdentityObligation
    problem massSq FieldClass base
    (spatialGreenIdentityObligationOfBoundaryFluxRepresentation
      problem representation)

/-- Boundary-flux representation evidence feeds A2A12. -/
def trueScalarKineticCandidateOfBoundaryFluxRepresentation
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (base :
      SpatialLaplacianCandidateWithoutGreenIdentity
        problem massSq FieldClass)
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    TrueScalarKineticOperatorCandidate problem massSq FieldClass :=
  trueScalarKineticCandidateOfSpatialGreenIdentity
    problem massSq FieldClass base
    (spatialGreenIdentityObligationOfBoundaryFluxRepresentation
      problem representation)

/-- Boundary-flux representation evidence feeds A2A10 domain closure. -/
def nonzeroDomainClosureOfBoundaryFluxRepresentation
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (base :
      SpatialLaplacianCandidateWithoutGreenIdentity
        problem massSq FieldClass)
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass :=
  nonzeroDomainClosureOfSpatialGreenIdentity
    problem massSq FieldClass base
    (spatialGreenIdentityObligationOfBoundaryFluxRepresentation
      problem representation)

/-- Boundary-flux representation evidence feeds A2A9 residual admissibility. -/
def residualAdmissibilityOfBoundaryFluxRepresentation
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (base :
      SpatialLaplacianCandidateWithoutGreenIdentity
        problem massSq FieldClass)
    (representation :
      SpatialLaplacianBoundaryFluxRepresentation problem) :
    RestrictedKGResidualAdmissibility
      problem.kineticOperator massSq FieldClass :=
  residualAdmissibilityOfSpatialGreenIdentity
    problem massSq FieldClass base
    (spatialGreenIdentityObligationOfBoundaryFluxRepresentation
      problem representation)

/-- Current support status for the boundary-flux representation dependency. -/
structure SpatialBoundaryFluxRepresentationCurrentSupportStatus where
  concrete_boundary_term_derivation_available : Prop
  concrete_boundary_term_derivation_not_available :
    Not concrete_boundary_term_derivation_available
  trace_normal_derivative_semantics_available : Prop
  trace_normal_derivative_semantics_not_available :
    Not trace_normal_derivative_semantics_available
  raw_to_two_sided_flux_theorem_available : Prop
  raw_to_two_sided_flux_theorem_not_available :
    Not raw_to_two_sided_flux_theorem_available
  domain_regular_for_boundary_evaluation_available : Prop
  domain_regular_for_boundary_evaluation_not_available :
    Not domain_regular_for_boundary_evaluation_available
  concrete_boundary_flux_representation_proved : Prop
  concrete_boundary_flux_representation_not_proved :
    Not concrete_boundary_flux_representation_proved
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/-- Current-support status: concrete flux representation remains retained. -/
def spatialBoundaryFluxRepresentationCurrentSupportStatusV0 :
    SpatialBoundaryFluxRepresentationCurrentSupportStatus where
  concrete_boundary_term_derivation_available := False
  concrete_boundary_term_derivation_not_available := by
    intro h
    exact h
  trace_normal_derivative_semantics_available := False
  trace_normal_derivative_semantics_not_available := by
    intro h
    exact h
  raw_to_two_sided_flux_theorem_available := False
  raw_to_two_sided_flux_theorem_not_available := by
    intro h
    exact h
  domain_regular_for_boundary_evaluation_available := False
  domain_regular_for_boundary_evaluation_not_available := by
    intro h
    exact h
  concrete_boundary_flux_representation_proved := False
  concrete_boundary_flux_representation_not_proved := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Status readout for this bounded boundary-flux representation surface. -/
structure SpatialBoundaryFluxRepresentationStatus where
  raw_boundary_flux_statement_defined : Prop
  representation_statement_defined : Prop
  representation_package_defined : Prop
  green_identity_reduction_recorded : Prop
  bridge_to_a2a14_recorded : Prop
  bridge_to_a2a13_recorded : Prop
  bridge_to_a2a12_recorded : Prop
  bridge_to_a2a10_recorded : Prop
  bridge_to_a2a9_recorded : Prop
  concrete_boundary_flux_representation_proved : Prop
  concrete_boundary_flux_representation_not_proved :
    Not concrete_boundary_flux_representation_proved
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this bounded A2A15 surface. -/
def spatialBoundaryFluxRepresentationStatusV0 :
    SpatialBoundaryFluxRepresentationStatus where
  raw_boundary_flux_statement_defined := True
  representation_statement_defined := True
  representation_package_defined := True
  green_identity_reduction_recorded := True
  bridge_to_a2a14_recorded := True
  bridge_to_a2a13_recorded := True
  bridge_to_a2a12_recorded := True
  bridge_to_a2a10_recorded := True
  bridge_to_a2a9_recorded := True
  concrete_boundary_flux_representation_proved := False
  concrete_boundary_flux_representation_not_proved := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A14SpatialLaplacianGreenIdentityRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId
  outcome_id := spatialBoundaryFluxRepresentationOutcomeId

/-- Short proof-facing alias. -/
def sbfrStatusV0 : SpatialBoundaryFluxRepresentationStatus :=
  spatialBoundaryFluxRepresentationStatusV0

/-- The raw boundary flux statement is defined. -/
theorem spatial_boundary_flux_raw_statement_defined_v0 :
    sbfrStatusV0.raw_boundary_flux_statement_defined := by
  trivial

/-- The representation statement is defined. -/
theorem spatial_boundary_flux_representation_statement_defined_v0 :
    sbfrStatusV0.representation_statement_defined := by
  trivial

/-- The representation package is defined. -/
theorem spatial_boundary_flux_representation_package_defined_v0 :
    sbfrStatusV0.representation_package_defined := by
  trivial

/-- The reduction to the A2A14 Green identity is recorded. -/
theorem spatial_boundary_flux_green_identity_reduction_v0 :
    sbfrStatusV0.green_identity_reduction_recorded := by
  trivial

/-- The bridge into A2A14 is recorded. -/
theorem spatial_boundary_flux_bridge_to_a2a14_v0 :
    sbfrStatusV0.bridge_to_a2a14_recorded := by
  trivial

/-- The bridge into A2A13 is recorded. -/
theorem spatial_boundary_flux_bridge_to_a2a13_v0 :
    sbfrStatusV0.bridge_to_a2a13_recorded := by
  trivial

/-- The bridge into A2A12 is recorded. -/
theorem spatial_boundary_flux_bridge_to_a2a12_v0 :
    sbfrStatusV0.bridge_to_a2a12_recorded := by
  trivial

/-- The bridge into A2A10 is recorded. -/
theorem spatial_boundary_flux_bridge_to_a2a10_v0 :
    sbfrStatusV0.bridge_to_a2a10_recorded := by
  trivial

/-- The bridge into A2A9 is recorded. -/
theorem spatial_boundary_flux_bridge_to_a2a9_v0 :
    sbfrStatusV0.bridge_to_a2a9_recorded := by
  trivial

/-- No concrete boundary-flux representation theorem is proved in this slice. -/
theorem spatial_boundary_flux_representation_not_proved_v0 :
    Not sbfrStatusV0.concrete_boundary_flux_representation_proved := by
  exact sbfrStatusV0.concrete_boundary_flux_representation_not_proved

/-- The attempt exposes the parent retained blocker id. -/
theorem spatial_boundary_flux_parent_retained_id_v0 :
    spatialBoundaryFluxRepresentationStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A14SpatialLaplacianGreenIdentityRetainedId := by
  simp [spatialBoundaryFluxRepresentationStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem spatial_boundary_flux_retained_id_v0 :
    spatialBoundaryFluxRepresentationStatusV0.retained_blocker_id =
      phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId := by
  simp [spatialBoundaryFluxRepresentationStatusV0]

/-- The attempt exposes the outcome id. -/
theorem spatial_boundary_flux_outcome_id_v0 :
    spatialBoundaryFluxRepresentationStatusV0.outcome_id =
      spatialBoundaryFluxRepresentationOutcomeId := by
  simp [spatialBoundaryFluxRepresentationStatusV0]

/-- Phase 2 remains unauthorized after this boundary-flux surface. -/
theorem spatial_boundary_flux_phase2_not_authorized_v0 :
    Not spatialBoundaryFluxRepresentationStatusV0.phase2Authorized := by
  exact spatialBoundaryFluxRepresentationStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained boundary-flux route. -/
def phase1Blocker003A2A15SpatialBoundaryFluxRepresentationV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a15_boundary_flux_v0_phase2_not_authorized :
    Not phase1Blocker003A2A15SpatialBoundaryFluxRepresentationV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumSpatialLaplacianBoundaryFluxRepresentation
end QFT
end ToeFormal
