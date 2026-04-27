/-
ToeFormal/QFT/ContinuumSpatialLaplacianKineticCandidate.lean

Spatial Laplacian kinetic candidate surface for PHASE1-BLOCKER-003A2A13.

Scope:
- choose the spatial Laplacian branch of the true scalar kinetic operator
  interface
- record the function-space, Laplacian-semantics, domain-closure, trace, and
  Green-identity obligations needed by that branch
- prove that supplied spatial-Laplacian evidence feeds the A2A12 true-operator
  route, A2A10 domain-closure route, and A2A9 residual-admissibility route
- keep actual derivative/Laplacian construction, concrete function space,
  trace theorem, nonzero Green identity proof, separating test class, full-field
  route recovery, and Phase 2 authorization out of scope
-/

import ToeFormal.QFT.ContinuumTrueScalarKineticOperatorCandidate

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialLaplacianKineticCandidate

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumResidualAdmissibility
open ContinuumNonzeroScalarKineticOperatorDomainClosure
open ContinuumTrueScalarKineticOperatorCandidate

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the spatial Laplacian candidate surface. -/
def phase1Blocker003A2A13SpatialLaplacianKineticCandidateRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A13_SPATIAL_LAPLACIAN_KINETIC_" ++
    "CANDIDATE_RETAINED"

/-- Outcome id for this bounded spatial Laplacian candidate surface. -/
def spatialLaplacianKineticCandidateOutcomeId : String :=
  "SPATIAL_LAPLACIAN_KINETIC_CANDIDATE_INTERFACE_RECORDED_" ++
    "CONSTRUCTION_RETAINED"

/-- Missing objects after the spatial Laplacian candidate surface. -/
inductive Phase1Blocker003A2A13MissingObject where
  | concreteSpatialFunctionSpace
  | spatialDerivativeSemantics
  | spatialLaplacianConstruction
  | spatialLaplacianLinearity
  | spatialLaplacianNonzeroWitness
  | restrictedDomainClosure
  | traceBoundaryCompatibility
  | spatialGreenIdentity
  | concreteSeparatingTestClass
  | fullFieldContinuumRouteRecovery
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A13 objects. -/
def phase1Blocker003A2A13MissingObjectId :
    Phase1Blocker003A2A13MissingObject -> String
  | .concreteSpatialFunctionSpace =>
      "003A2A13_CONCRETE_SPATIAL_FUNCTION_SPACE_RETAINED"
  | .spatialDerivativeSemantics =>
      "003A2A13_SPATIAL_DERIVATIVE_SEMANTICS_RETAINED"
  | .spatialLaplacianConstruction =>
      "003A2A13_SPATIAL_LAPLACIAN_CONSTRUCTION_RETAINED"
  | .spatialLaplacianLinearity =>
      "003A2A13_SPATIAL_LAPLACIAN_LINEARITY_RETAINED"
  | .spatialLaplacianNonzeroWitness =>
      "003A2A13_SPATIAL_LAPLACIAN_NONZERO_WITNESS_RETAINED"
  | .restrictedDomainClosure =>
      "003A2A13_RESTRICTED_DOMAIN_CLOSURE_RETAINED"
  | .traceBoundaryCompatibility =>
      "003A2A13_TRACE_BOUNDARY_COMPATIBILITY_RETAINED"
  | .spatialGreenIdentity =>
      "003A2A13_SPATIAL_GREEN_IDENTITY_RETAINED"
  | .concreteSeparatingTestClass =>
      "003A2A13_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"
  | .fullFieldContinuumRouteRecovery =>
      "003A2A13_FULL_FIELD_CONTINUUM_ROUTE_RECOVERY_RETAINED"

/-- The explicit remaining objects after this bounded surface. -/
def phase1Blocker003A2A13MissingObjectsV0 :
    List Phase1Blocker003A2A13MissingObject :=
  [ .concreteSpatialFunctionSpace
  , .spatialDerivativeSemantics
  , .spatialLaplacianConstruction
  , .spatialLaplacianLinearity
  , .spatialLaplacianNonzeroWitness
  , .restrictedDomainClosure
  , .traceBoundaryCompatibility
  , .spatialGreenIdentity
  , .concreteSeparatingTestClass
  , .fullFieldContinuumRouteRecovery
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a13_missing_objects_v0_expected :
    phase1Blocker003A2A13MissingObjectsV0 =
      [ .concreteSpatialFunctionSpace
      , .spatialDerivativeSemantics
      , .spatialLaplacianConstruction
      , .spatialLaplacianLinearity
      , .spatialLaplacianNonzeroWitness
      , .restrictedDomainClosure
      , .traceBoundaryCompatibility
      , .spatialGreenIdentity
      , .concreteSeparatingTestClass
      , .fullFieldContinuumRouteRecovery
      ] := by
  rfl

/--
Spatial Laplacian branch of the true scalar kinetic operator route.

This is an evidence package, not a construction of a Laplacian.  It records the
calculus and boundary facts a concrete spatial-Laplacian model must supply
before the true-operator route can be promoted beyond retained status.
-/
structure SpatialLaplacianKineticCandidate {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop) where
  selected_problem : ScalarKineticBoundaryProblemSelected problem
  concrete_spatial_function_space : Prop
  concrete_spatial_function_space_supplied :
    concrete_spatial_function_space
  spatial_derivative_semantics : Prop
  spatial_derivative_semantics_supplied :
    spatial_derivative_semantics
  spatial_laplacian_operator_selected : Prop
  spatial_laplacian_operator_selected_supplied :
    spatial_laplacian_operator_selected
  spatial_geometry_or_coordinate_data : Prop
  spatial_geometry_or_coordinate_data_supplied :
    spatial_geometry_or_coordinate_data
  boundary_trace_compatible_with_laplacian : Prop
  boundary_trace_compatible_with_laplacian_supplied :
    boundary_trace_compatible_with_laplacian
  operator_linear : LinearOperator problem.kineticOperator
  operator_nonzero : ScalarKineticOperatorNonzero problem.kineticOperator
  admitted_fields_in_operator_domain :
    forall phi : ContinuumField Point,
      FieldClass phi -> problem.InOperatorDomain phi
  admitted_fields_trace_vanishing :
    forall phi : ContinuumField Point,
      FieldClass phi -> TraceVanishingCompactSupportOrDecay problem phi
  operator_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (problem.kineticOperator phi)
  mass_term_maps_admitted :
    forall phi : ContinuumField Point,
      FieldClass phi -> FieldClass (fieldSMul massSq phi)
  add_closed :
    forall x y : ContinuumField Point,
      FieldClass x -> FieldClass y -> FieldClass (fieldAdd x y)
  green_identity_for_spatial_laplacian :
    forall x y : ContinuumField Point,
      problem.InOperatorDomain x ->
      problem.InOperatorDomain y ->
        ContinuumPair problem.integral x (problem.kineticOperator y) =
          ContinuumPair problem.integral y (problem.kineticOperator x) +
            twoSidedBoundaryFlux problem.trace x y

/-- A supplied spatial-Laplacian candidate is a true-operator candidate. -/
def trueScalarKineticOperatorCandidateOfSpatialLaplacian
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate :
      SpatialLaplacianKineticCandidate problem massSq FieldClass) :
    TrueScalarKineticOperatorCandidate problem massSq FieldClass where
  operator_kind := TrueScalarKineticOperatorKind.spatialLaplacian
  selected_problem := candidate.selected_problem
  concrete_calculus_function_space :=
    candidate.concrete_spatial_function_space
  concrete_calculus_function_space_supplied :=
    candidate.concrete_spatial_function_space_supplied
  derivative_or_laplacian_semantics :=
    candidate.spatial_derivative_semantics
  derivative_or_laplacian_semantics_supplied :=
    candidate.spatial_derivative_semantics_supplied
  metric_or_geometric_kinetic_data :=
    candidate.spatial_geometry_or_coordinate_data
  metric_or_geometric_kinetic_data_supplied :=
    candidate.spatial_geometry_or_coordinate_data_supplied
  operator_linear := candidate.operator_linear
  operator_nonzero := candidate.operator_nonzero
  admitted_fields_in_operator_domain :=
    candidate.admitted_fields_in_operator_domain
  admitted_fields_trace_vanishing :=
    candidate.admitted_fields_trace_vanishing
  operator_maps_admitted := candidate.operator_maps_admitted
  mass_term_maps_admitted := candidate.mass_term_maps_admitted
  add_closed := candidate.add_closed
  green_identity_for_true_operator :=
    candidate.green_identity_for_spatial_laplacian

/-- The selected true-operator kind is the spatial Laplacian branch. -/
theorem true_candidate_kind_of_spatial_laplacian
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate :
      SpatialLaplacianKineticCandidate problem massSq FieldClass) :
    (trueScalarKineticOperatorCandidateOfSpatialLaplacian
      problem massSq FieldClass candidate).operator_kind =
        TrueScalarKineticOperatorKind.spatialLaplacian := by
  rfl

/-- A supplied spatial-Laplacian candidate gives the A2A10 closure package. -/
def nonzeroDomainClosureOfSpatialLaplacianCandidate
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate :
      SpatialLaplacianKineticCandidate problem massSq FieldClass) :
    NonzeroScalarKineticOperatorDomainClosure problem massSq FieldClass :=
  nonzeroDomainClosureOfTrueScalarKineticOperatorCandidate
    problem massSq FieldClass
    (trueScalarKineticOperatorCandidateOfSpatialLaplacian
      problem massSq FieldClass candidate)

/-- A supplied spatial-Laplacian candidate gives A2A9 residual admissibility. -/
def residualAdmissibilityOfSpatialLaplacianCandidate
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (massSq : Real)
    (FieldClass : ContinuumField Point -> Prop)
    (candidate :
      SpatialLaplacianKineticCandidate problem massSq FieldClass) :
    RestrictedKGResidualAdmissibility
      problem.kineticOperator massSq FieldClass :=
  residualAdmissibilityOfTrueScalarKineticOperatorCandidate
    problem massSq FieldClass
    (trueScalarKineticOperatorCandidateOfSpatialLaplacian
      problem massSq FieldClass candidate)

/-- A supplied spatial-Laplacian candidate gives the selected Green identity. -/
theorem spatial_laplacian_candidate_green_identity
    {Point : Type}
    {problem : ScalarKineticBoundaryProblem Point}
    {massSq : Real}
    {FieldClass : ContinuumField Point -> Prop}
    (candidate :
      SpatialLaplacianKineticCandidate problem massSq FieldClass)
    (x y : ContinuumField Point)
    (hx : problem.InOperatorDomain x)
    (hy : problem.InOperatorDomain y) :
    ContinuumPair problem.integral x (problem.kineticOperator y) =
      ContinuumPair problem.integral y (problem.kineticOperator x) +
        twoSidedBoundaryFlux problem.trace x y := by
  exact candidate.green_identity_for_spatial_laplacian x y hx hy

/-- Current support status for the spatial-Laplacian branch. -/
structure SpatialLaplacianCurrentSupportStatus where
  concrete_spatial_function_space_available : Prop
  concrete_spatial_function_space_not_available :
    Not concrete_spatial_function_space_available
  spatial_derivative_semantics_available : Prop
  spatial_derivative_semantics_not_available :
    Not spatial_derivative_semantics_available
  spatial_laplacian_construction_available : Prop
  spatial_laplacian_construction_not_available :
    Not spatial_laplacian_construction_available
  trace_compatibility_theorem_available : Prop
  trace_compatibility_theorem_not_available :
    Not trace_compatibility_theorem_available
  spatial_green_identity_available : Prop
  spatial_green_identity_not_available :
    Not spatial_green_identity_available
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/-- Current-support status: the spatial Laplacian construction is retained. -/
def spatialLaplacianCurrentSupportStatusV0 :
    SpatialLaplacianCurrentSupportStatus where
  concrete_spatial_function_space_available := False
  concrete_spatial_function_space_not_available := by
    intro h
    exact h
  spatial_derivative_semantics_available := False
  spatial_derivative_semantics_not_available := by
    intro h
    exact h
  spatial_laplacian_construction_available := False
  spatial_laplacian_construction_not_available := by
    intro h
    exact h
  trace_compatibility_theorem_available := False
  trace_compatibility_theorem_not_available := by
    intro h
    exact h
  spatial_green_identity_available := False
  spatial_green_identity_not_available := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Status readout for this bounded spatial-Laplacian candidate surface. -/
structure SpatialLaplacianKineticCandidateAttemptStatus where
  spatial_laplacian_interface_defined : Prop
  true_operator_bridge_recorded : Prop
  domain_closure_bridge_recorded : Prop
  residual_admissibility_bridge_recorded : Prop
  green_identity_obligation_recorded : Prop
  current_support_status_recorded : Prop
  concrete_spatial_laplacian_constructed : Prop
  concrete_spatial_laplacian_not_constructed :
    Not concrete_spatial_laplacian_constructed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this bounded spatial-Laplacian surface. -/
def spatialLaplacianKineticCandidateAttemptStatusV0 :
    SpatialLaplacianKineticCandidateAttemptStatus where
  spatial_laplacian_interface_defined := True
  true_operator_bridge_recorded := True
  domain_closure_bridge_recorded := True
  residual_admissibility_bridge_recorded := True
  green_identity_obligation_recorded := True
  current_support_status_recorded := True
  concrete_spatial_laplacian_constructed := False
  concrete_spatial_laplacian_not_constructed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A12TrueScalarKineticOperatorRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A13SpatialLaplacianKineticCandidateRetainedId
  outcome_id := spatialLaplacianKineticCandidateOutcomeId

/-- Short local status alias. -/
def spatialLaplacianKineticCandidateStatusV0 :
    SpatialLaplacianKineticCandidateAttemptStatus :=
  spatialLaplacianKineticCandidateAttemptStatusV0

/-- Short proof-facing alias. -/
def slkCandidateStatusV0 :
    SpatialLaplacianKineticCandidateAttemptStatus :=
  spatialLaplacianKineticCandidateStatusV0

/-- The spatial-Laplacian candidate interface is defined. -/
theorem spatial_laplacian_candidate_interface_defined_v0 :
    slkCandidateStatusV0.spatial_laplacian_interface_defined := by
  trivial

/-- The bridge into A2A12 true-operator evidence is recorded. -/
theorem spatial_laplacian_candidate_true_operator_bridge_v0 :
    slkCandidateStatusV0.true_operator_bridge_recorded := by
  trivial

/-- The bridge into A2A10 domain closure is recorded. -/
theorem spatial_laplacian_candidate_domain_closure_bridge_v0 :
    slkCandidateStatusV0.domain_closure_bridge_recorded := by
  trivial

/-- The bridge into A2A9 residual admissibility is recorded. -/
theorem spatial_laplacian_candidate_residual_admissibility_bridge_v0 :
    slkCandidateStatusV0.residual_admissibility_bridge_recorded := by
  trivial

/-- The Green-identity obligation for the spatial branch is recorded. -/
theorem spatial_laplacian_candidate_green_identity_obligation_v0 :
    slkCandidateStatusV0.green_identity_obligation_recorded := by
  trivial

/-- The current-support gap readout is recorded. -/
theorem spatial_laplacian_candidate_current_support_recorded_v0 :
    slkCandidateStatusV0.current_support_status_recorded := by
  trivial

/-- No concrete spatial Laplacian is constructed in this slice. -/
theorem spatial_laplacian_not_constructed_v0 :
    Not slkCandidateStatusV0.concrete_spatial_laplacian_constructed := by
  exact slkCandidateStatusV0.concrete_spatial_laplacian_not_constructed

/-- The attempt exposes the parent retained blocker id. -/
theorem spatial_laplacian_candidate_parent_retained_id_v0 :
    spatialLaplacianKineticCandidateStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A12TrueScalarKineticOperatorRetainedId := by
  simp [spatialLaplacianKineticCandidateStatusV0,
    spatialLaplacianKineticCandidateAttemptStatusV0]

/-- The attempt exposes the retained blocker id. -/
theorem spatial_laplacian_candidate_retained_id_v0 :
    spatialLaplacianKineticCandidateStatusV0.retained_blocker_id =
      phase1Blocker003A2A13SpatialLaplacianKineticCandidateRetainedId := by
  simp [spatialLaplacianKineticCandidateStatusV0,
    spatialLaplacianKineticCandidateAttemptStatusV0]

/-- The attempt exposes the outcome id. -/
theorem spatial_laplacian_candidate_outcome_id_v0 :
    spatialLaplacianKineticCandidateStatusV0.outcome_id =
      spatialLaplacianKineticCandidateOutcomeId := by
  simp [spatialLaplacianKineticCandidateStatusV0,
    spatialLaplacianKineticCandidateAttemptStatusV0]

/-- Phase 2 remains unauthorized after this spatial-Laplacian surface. -/
theorem spatial_laplacian_candidate_phase2_not_authorized_v0 :
    Not spatialLaplacianKineticCandidateStatusV0.phase2Authorized := by
  exact spatialLaplacianKineticCandidateStatusV0.phase2_not_authorized

/-- Parent Blocker 003 readout for this retained spatial-Laplacian route. -/
def phase1Blocker003A2A13SpatialLaplacianKineticCandidateV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a13_spatial_laplacian_v0_phase2_not_authorized :
    Not phase1Blocker003A2A13SpatialLaplacianKineticCandidateV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumSpatialLaplacianKineticCandidate
end QFT
end ToeFormal
