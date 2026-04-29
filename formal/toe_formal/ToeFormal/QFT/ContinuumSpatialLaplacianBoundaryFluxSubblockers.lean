/-
ToeFormal/QFT/ContinuumSpatialLaplacianBoundaryFluxSubblockers.lean

Retained sub-blocker split for PHASE1-BLOCKER-003A2A15.

Scope:
- split the A2A15 spatial boundary-flux representation blocker into the next
  concrete analytic proof targets
- show that supplied raw spatial IBP plus supplied boundary-flux
  representation evidence still feeds the existing A2A15 route
- keep concrete proof, Phase 2 authorization, seam closure, empirical
  validation, and master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialLaplacianBoundaryFluxRepresentation

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialLaplacianBoundaryFluxSubblockers

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumSpatialLaplacianKineticCandidate
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation

set_option autoImplicit false

noncomputable section

/-- Retained blocker after splitting the A2A15 boundary-flux target. -/
def phase1Blocker003A2A15SubblockerSplitRetainedId : String :=
  "PHASE1-BLOCKER-003A2A15_SPATIAL_LAPLACIAN_BOUNDARY_FLUX_" ++
    "SUBBLOCKERS_SPLIT_RETAINED"

/-- Outcome id for the retained A2A15 sub-blocker split. -/
def spatialBoundaryFluxSubblockerSplitOutcomeId : String :=
  "SPATIAL_LAPLACIAN_BOUNDARY_FLUX_SUBBLOCKERS_SPLIT_RETAINED"

/--
The next retained proof targets under A2A15.

These are proof obligations, not completed analytic theorems.
-/
inductive Phase1Blocker003A2A15RetainedSubblocker where
  | rawSpatialIntegrationByParts
  | boundaryFluxRepresentation
  | regularityDomainAssumptions
  | traceCompatibility
  | orientationConvention
  | concreteLaplacianConstruction
  | separatingTestClass
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A2A15 sub-blockers. -/
def phase1Blocker003A2A15RetainedSubblockerId :
    Phase1Blocker003A2A15RetainedSubblocker -> String
  | .rawSpatialIntegrationByParts =>
      "003A2A15_RAW_SPATIAL_INTEGRATION_BY_PARTS_RETAINED"
  | .boundaryFluxRepresentation =>
      "003A2A15_BOUNDARY_FLUX_REPRESENTATION_RETAINED"
  | .regularityDomainAssumptions =>
      "003A2A15_REGULARITY_DOMAIN_ASSUMPTIONS_RETAINED"
  | .traceCompatibility =>
      "003A2A15_TRACE_COMPATIBILITY_RETAINED"
  | .orientationConvention =>
      "003A2A15_ORIENTATION_CONVENTION_RETAINED"
  | .concreteLaplacianConstruction =>
      "003A2A15_CONCRETE_LAPLACIAN_CONSTRUCTION_RETAINED"
  | .separatingTestClass =>
      "003A2A15_SEPARATING_TEST_CLASS_RETAINED"

/-- The retained A2A15 sub-blocker list is stable and explicit. -/
def phase1Blocker003A2A15RetainedSubblockersV0 :
    List Phase1Blocker003A2A15RetainedSubblocker :=
  [ .rawSpatialIntegrationByParts
  , .boundaryFluxRepresentation
  , .regularityDomainAssumptions
  , .traceCompatibility
  , .orientationConvention
  , .concreteLaplacianConstruction
  , .separatingTestClass
  ]

/-- Readout theorem for the retained A2A15 sub-blocker split. -/
theorem phase1_blocker003a2a15_retained_subblockers_v0_expected :
    phase1Blocker003A2A15RetainedSubblockersV0 =
      [ .rawSpatialIntegrationByParts
      , .boundaryFluxRepresentation
      , .regularityDomainAssumptions
      , .traceCompatibility
      , .orientationConvention
      , .concreteLaplacianConstruction
      , .separatingTestClass
      ] := by
  rfl

/--
Evidence package for the split A2A15 target.

The package separates the retained proof obligations while preserving the
existing conditional route into `SpatialLaplacianBoundaryFluxRepresentation`.
-/
structure SpatialBoundaryFluxSubblockerEvidence {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  selected_problem : ScalarKineticBoundaryProblemSelected problem
  raw_boundary_flux : RawSpatialBoundaryFlux Point
  raw_spatial_integration_by_parts_source : Prop
  raw_spatial_integration_by_parts_source_supplied :
    raw_spatial_integration_by_parts_source
  raw_spatial_integration_by_parts_statement :
    RawSpatialIntegrationByPartsStatement problem raw_boundary_flux
  boundary_flux_representation_source : Prop
  boundary_flux_representation_source_supplied :
    boundary_flux_representation_source
  boundary_flux_representation_statement :
    BoundaryFluxRepresentationStatement problem raw_boundary_flux
  regularity_domain_assumptions : Prop
  regularity_domain_assumptions_supplied :
    regularity_domain_assumptions
  trace_compatibility : Prop
  trace_compatibility_supplied : trace_compatibility
  trace_normal_derivative_semantics : Prop
  trace_normal_derivative_semantics_supplied :
    trace_normal_derivative_semantics
  orientation_convention : Prop
  orientation_convention_supplied : orientation_convention
  concrete_laplacian_construction : Prop
  concrete_laplacian_construction_supplied :
    concrete_laplacian_construction
  separating_test_class : Prop
  separating_test_class_supplied : separating_test_class

/--
The retained split is only a refinement of the existing A2A15 conditional
evidence route.
-/
def boundaryFluxRepresentationOfSubblockerEvidence
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (evidence : SpatialBoundaryFluxSubblockerEvidence problem) :
    SpatialLaplacianBoundaryFluxRepresentation problem where
  selected_problem := evidence.selected_problem
  spatial_laplacian_operator_selected :=
    evidence.concrete_laplacian_construction
  spatial_laplacian_operator_selected_supplied :=
    evidence.concrete_laplacian_construction_supplied
  raw_boundary_flux := evidence.raw_boundary_flux
  concrete_spatial_integration_by_parts_source :=
    evidence.raw_spatial_integration_by_parts_source
  concrete_spatial_integration_by_parts_source_supplied :=
    evidence.raw_spatial_integration_by_parts_source_supplied
  spatial_boundary_trace_theorem := evidence.trace_compatibility
  spatial_boundary_trace_theorem_supplied :=
    evidence.trace_compatibility_supplied
  spatial_laplacian_domain_regular :=
    evidence.regularity_domain_assumptions
  spatial_laplacian_domain_regular_supplied :=
    evidence.regularity_domain_assumptions_supplied
  trace_normal_derivative_semantics :=
    evidence.trace_normal_derivative_semantics
  trace_normal_derivative_semantics_supplied :=
    evidence.trace_normal_derivative_semantics_supplied
  boundary_orientation_sign_convention :=
    evidence.orientation_convention
  boundary_orientation_sign_convention_supplied :=
    evidence.orientation_convention_supplied
  raw_integration_by_parts :=
    evidence.raw_spatial_integration_by_parts_statement
  boundary_flux_representation :=
    evidence.boundary_flux_representation_statement

/-- Supplied split evidence still gives the A2A14 Green-identity statement. -/
theorem spatial_green_identity_statement_of_subblocker_evidence
    {Point : Type}
    {problem : ScalarKineticBoundaryProblem Point}
    (evidence : SpatialBoundaryFluxSubblockerEvidence problem) :
    SpatialLaplacianGreenIdentityStatement problem :=
  spatial_green_identity_statement_of_boundary_flux_representation
    (boundaryFluxRepresentationOfSubblockerEvidence problem evidence)

/-- Supplied split evidence feeds the existing A2A15-to-A2A14 obligation. -/
def spatialGreenIdentityObligationOfSubblockerEvidence
    {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (evidence : SpatialBoundaryFluxSubblockerEvidence problem) :
    SpatialLaplacianGreenIdentityObligation problem :=
  spatialGreenIdentityObligationOfBoundaryFluxRepresentation
    problem
    (boundaryFluxRepresentationOfSubblockerEvidence problem evidence)

/-- The retained split does not authorize Phase 2. -/
theorem phase1_blocker003a2a15_subblocker_split_phase2_not_authorized :
    phase1Blocker003A2A15SubblockerSplitRetainedId ≠
      "PHASE2_AUTHORIZED" := by
  decide

/-- The retained split does not claim A2A15 closure. -/
theorem phase1_blocker003a2a15_subblocker_split_retains_parent_blocker :
    phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId =
      "PHASE1-BLOCKER-003A2A15_SPATIAL_LAPLACIAN_BOUNDARY_FLUX_" ++
        "REPRESENTATION_RETAINED" := by
  rfl

end

end ContinuumSpatialLaplacianBoundaryFluxSubblockers
end QFT
end ToeFormal
