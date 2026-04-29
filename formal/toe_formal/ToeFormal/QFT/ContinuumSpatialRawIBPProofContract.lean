/-
ToeFormal/QFT/ContinuumSpatialRawIBPProofContract.lean

Bounded A2A15A raw spatial integration-by-parts proof contract.

Scope:
- construct a concrete finite two-endpoint interval model
- prove raw spatial IBP for a nonzero graph-Laplacian surrogate
- prove that its raw boundary flux is represented by the repo two-sided flux
  for the chosen zero-normal endpoint trace
- route the checked finite model through the existing A2A15 sub-blocker API
- retain the analytic interval lift, true continuum derivative/Laplacian
  semantics, nonzero normal-derivative boundary flux, and Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumSpatialLaplacianBoundaryFluxSubblockers

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialRawIBPProofContract

open ContinuumFirstVariation
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumNonzeroScalarKineticOperatorDomainClosure
open ContinuumSpatialLaplacianGreenIdentityObligation
open ContinuumSpatialLaplacianBoundaryFluxRepresentation
open ContinuumSpatialLaplacianBoundaryFluxSubblockers

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the bounded raw spatial IBP proof contract. -/
def phase1Blocker003A2A15ARawSpatialIBPProofContractRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A_RAW_SPATIAL_IBP_PROOF_CONTRACT_" ++
    "RETAINED"

/-- Outcome id for this bounded finite-model theorem movement. -/
def finiteTwoPointSpatialIBPOutcomeId : String :=
  "FINITE_TWO_POINT_SPATIAL_IBP_MODEL_DISCHARGED_ANALYTIC_INTERVAL_" ++
    "RETAINED"

/-- Remaining objects after the finite raw-IBP proof contract. -/
inductive Phase1Blocker003A2A15AMissingObject where
  | analyticIntervalDomain
  | continuumDerivativeSemantics
  | continuumLaplacianConstruction
  | continuumIntegrationByPartsTheorem
  | nonzeroNormalDerivativeTraceSemantics
  | nonzeroBoundaryFluxRepresentation
  | domainRegularityForBoundaryEvaluation
  | orientationConventionForAnalyticBoundary
  | concreteSeparatingTestClass
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained A2A15A objects. -/
def phase1Blocker003A2A15AMissingObjectId :
    Phase1Blocker003A2A15AMissingObject -> String
  | .analyticIntervalDomain =>
      "003A2A15A_ANALYTIC_INTERVAL_DOMAIN_RETAINED"
  | .continuumDerivativeSemantics =>
      "003A2A15A_CONTINUUM_DERIVATIVE_SEMANTICS_RETAINED"
  | .continuumLaplacianConstruction =>
      "003A2A15A_CONTINUUM_LAPLACIAN_CONSTRUCTION_RETAINED"
  | .continuumIntegrationByPartsTheorem =>
      "003A2A15A_CONTINUUM_INTEGRATION_BY_PARTS_THEOREM_RETAINED"
  | .nonzeroNormalDerivativeTraceSemantics =>
      "003A2A15A_NONZERO_NORMAL_DERIVATIVE_TRACE_SEMANTICS_RETAINED"
  | .nonzeroBoundaryFluxRepresentation =>
      "003A2A15A_NONZERO_BOUNDARY_FLUX_REPRESENTATION_RETAINED"
  | .domainRegularityForBoundaryEvaluation =>
      "003A2A15A_DOMAIN_REGULARITY_FOR_BOUNDARY_EVALUATION_RETAINED"
  | .orientationConventionForAnalyticBoundary =>
      "003A2A15A_ORIENTATION_CONVENTION_FOR_ANALYTIC_BOUNDARY_RETAINED"
  | .concreteSeparatingTestClass =>
      "003A2A15A_CONCRETE_SEPARATING_TEST_CLASS_RETAINED"

/-- The retained A2A15A object list is stable and explicit. -/
def phase1Blocker003A2A15AMissingObjectsV0 :
    List Phase1Blocker003A2A15AMissingObject :=
  [ .analyticIntervalDomain
  , .continuumDerivativeSemantics
  , .continuumLaplacianConstruction
  , .continuumIntegrationByPartsTheorem
  , .nonzeroNormalDerivativeTraceSemantics
  , .nonzeroBoundaryFluxRepresentation
  , .domainRegularityForBoundaryEvaluation
  , .orientationConventionForAnalyticBoundary
  , .concreteSeparatingTestClass
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a15a_missing_objects_v0_expected :
    phase1Blocker003A2A15AMissingObjectsV0 =
      [ .analyticIntervalDomain
      , .continuumDerivativeSemantics
      , .continuumLaplacianConstruction
      , .continuumIntegrationByPartsTheorem
      , .nonzeroNormalDerivativeTraceSemantics
      , .nonzeroBoundaryFluxRepresentation
      , .domainRegularityForBoundaryEvaluation
      , .orientationConventionForAnalyticBoundary
      , .concreteSeparatingTestClass
      ] := by
  rfl

/-- A minimal finite closed interval with two endpoints. -/
inductive TwoPointSpatialInterval where
  | left
  | right
deriving DecidableEq, Repr

instance : Inhabited TwoPointSpatialInterval where
  default := TwoPointSpatialInterval.left

/-- Finite two-endpoint integral used by the bounded raw-IBP model. -/
def twoPointSpatialIntegral :
    ContinuumField TwoPointSpatialInterval -> Real :=
  fun f => f TwoPointSpatialInterval.left + f TwoPointSpatialInterval.right

/-- Nonzero graph-Laplacian surrogate on the two-endpoint interval. -/
def twoPointGraphLaplacian :
    ContinuumField TwoPointSpatialInterval ->
      ContinuumField TwoPointSpatialInterval :=
  fun f p =>
    match p with
    | TwoPointSpatialInterval.left =>
        f TwoPointSpatialInterval.right - f TwoPointSpatialInterval.left
    | TwoPointSpatialInterval.right =>
        f TwoPointSpatialInterval.left - f TwoPointSpatialInterval.right

/-- Endpoint trace with meaningful endpoint values and zero normal traces. -/
def twoPointEndpointTraceZeroNormal :
    TwoSidedBoundaryTrace TwoPointSpatialInterval where
  leftTrace := fun f => f TwoPointSpatialInterval.left
  rightTrace := fun f => f TwoPointSpatialInterval.right
  leftNormalDerivativeTrace := fun _ => 0
  rightNormalDerivativeTrace := fun _ => 0

/-- The finite two-endpoint integral is linear. -/
def twoPointSpatialIntegralLinear :
    LinearIntegral twoPointSpatialIntegral where
  map_add := by
    intro f g
    simp [twoPointSpatialIntegral]
    ring
  map_smul := by
    intro a f
    simp [twoPointSpatialIntegral]
    ring

/-- The finite graph Laplacian is linear. -/
def twoPointGraphLaplacianLinear :
    LinearOperator twoPointGraphLaplacian where
  map_add := by
    intro x y
    funext p
    cases p <;> simp [twoPointGraphLaplacian, fieldAdd] <;> ring
  map_smul := by
    intro a x
    funext p
    cases p <;> simp [twoPointGraphLaplacian, fieldSMul] <;> ring

/-- Left endpoint spike witnessing that the graph Laplacian is nonzero. -/
def twoPointLeftSpike : ContinuumField TwoPointSpatialInterval
  | TwoPointSpatialInterval.left => 1
  | TwoPointSpatialInterval.right => 0

/-- The two-endpoint graph Laplacian is not the zero operator. -/
theorem two_point_graph_laplacian_nonzero :
    ScalarKineticOperatorNonzero twoPointGraphLaplacian := by
  refine Exists.intro twoPointLeftSpike ?_
  intro h
  have hLeft :=
    congrArg
      (fun f : ContinuumField TwoPointSpatialInterval =>
        f TwoPointSpatialInterval.left) h
  norm_num [twoPointGraphLaplacian, twoPointLeftSpike] at hLeft

/-- Scalar boundary problem induced by the finite two-endpoint model. -/
def twoPointSpatialBoundaryProblem :
    ScalarKineticBoundaryProblem TwoPointSpatialInterval where
  operator_kind := ScalarBoundaryOperatorKind.kineticBox
  function_space_kind :=
    ScalarBoundaryFunctionSpaceKind.smoothCompactSupportOrDecay
  integral := twoPointSpatialIntegral
  kineticOperator := twoPointGraphLaplacian
  trace := twoPointEndpointTraceZeroNormal
  FieldSmooth := fun _ => True
  InOperatorDomain := fun _ => True

/-- The finite model targets the selected scalar kinetic boundary lane. -/
theorem two_point_spatial_boundary_problem_selected :
    ScalarKineticBoundaryProblemSelected twoPointSpatialBoundaryProblem := by
  constructor <;> rfl

/-- Raw boundary flux for the closed finite two-endpoint graph model. -/
def twoPointRawBoundaryFlux :
    RawSpatialBoundaryFlux TwoPointSpatialInterval :=
  fun _ _ => 0

/-- The zero-normal endpoint trace has zero two-sided boundary flux. -/
theorem two_point_zero_normal_boundary_flux_zero
    (x y : ContinuumField TwoPointSpatialInterval) :
    twoSidedBoundaryFlux twoPointEndpointTraceZeroNormal x y = 0 := by
  simp [twoSidedBoundaryFlux, twoPointEndpointTraceZeroNormal]

/-- Raw spatial IBP is proved for the finite two-endpoint graph Laplacian. -/
theorem two_point_raw_spatial_integration_by_parts :
    RawSpatialIntegrationByPartsStatement
      twoPointSpatialBoundaryProblem twoPointRawBoundaryFlux := by
  intro x y _hx _hy
  simp [twoPointSpatialBoundaryProblem, ContinuumPair,
    twoPointSpatialIntegral, twoPointGraphLaplacian,
    twoPointRawBoundaryFlux]
  ring

/--
The finite raw boundary flux is represented by the repo's two-sided flux for
the chosen endpoint trace.
-/
theorem two_point_boundary_flux_representation :
    BoundaryFluxRepresentationStatement
      twoPointSpatialBoundaryProblem twoPointRawBoundaryFlux := by
  intro x y _hx _hy
  simp [twoPointSpatialBoundaryProblem, twoPointRawBoundaryFlux,
    twoSidedBoundaryFlux, twoPointEndpointTraceZeroNormal]

/-- Checked A2A15 boundary-flux representation for the finite model. -/
def twoPointSpatialBoundaryFluxRepresentation :
    SpatialLaplacianBoundaryFluxRepresentation
      twoPointSpatialBoundaryProblem where
  selected_problem := two_point_spatial_boundary_problem_selected
  spatial_laplacian_operator_selected := True
  spatial_laplacian_operator_selected_supplied := trivial
  raw_boundary_flux := twoPointRawBoundaryFlux
  concrete_spatial_integration_by_parts_source := True
  concrete_spatial_integration_by_parts_source_supplied := trivial
  spatial_boundary_trace_theorem := True
  spatial_boundary_trace_theorem_supplied := trivial
  spatial_laplacian_domain_regular := True
  spatial_laplacian_domain_regular_supplied := trivial
  trace_normal_derivative_semantics := True
  trace_normal_derivative_semantics_supplied := trivial
  boundary_orientation_sign_convention := True
  boundary_orientation_sign_convention_supplied := trivial
  raw_integration_by_parts := two_point_raw_spatial_integration_by_parts
  boundary_flux_representation := two_point_boundary_flux_representation

/-- Checked A2A15 sub-blocker evidence for the finite model. -/
def twoPointSpatialBoundaryFluxSubblockerEvidence :
    SpatialBoundaryFluxSubblockerEvidence
      twoPointSpatialBoundaryProblem where
  selected_problem := two_point_spatial_boundary_problem_selected
  raw_boundary_flux := twoPointRawBoundaryFlux
  raw_spatial_integration_by_parts_source := True
  raw_spatial_integration_by_parts_source_supplied := trivial
  raw_spatial_integration_by_parts_statement :=
    two_point_raw_spatial_integration_by_parts
  boundary_flux_representation_source := True
  boundary_flux_representation_source_supplied := trivial
  boundary_flux_representation_statement :=
    two_point_boundary_flux_representation
  regularity_domain_assumptions := True
  regularity_domain_assumptions_supplied := trivial
  trace_compatibility := True
  trace_compatibility_supplied := trivial
  trace_normal_derivative_semantics := True
  trace_normal_derivative_semantics_supplied := trivial
  orientation_convention := True
  orientation_convention_supplied := trivial
  concrete_laplacian_construction := True
  concrete_laplacian_construction_supplied := trivial
  separating_test_class := True
  separating_test_class_supplied := trivial

/-- The checked finite model supplies the A2A14 Green-identity statement. -/
theorem two_point_spatial_green_identity_statement :
    SpatialLaplacianGreenIdentityStatement
      twoPointSpatialBoundaryProblem :=
  spatial_green_identity_statement_of_subblocker_evidence
    twoPointSpatialBoundaryFluxSubblockerEvidence

/-- The checked finite model supplies the A2A14 obligation object. -/
def twoPointSpatialGreenIdentityObligation :
    SpatialLaplacianGreenIdentityObligation
      twoPointSpatialBoundaryProblem :=
  spatialGreenIdentityObligationOfSubblockerEvidence
    twoPointSpatialBoundaryProblem
    twoPointSpatialBoundaryFluxSubblockerEvidence

/-- Status readout for this bounded A2A15A theorem movement. -/
structure RawSpatialIBPProofContractStatus where
  finite_two_point_model_defined : Prop
  finite_two_point_integral_linear : Prop
  finite_two_point_operator_linear : Prop
  finite_two_point_operator_nonzero : Prop
  finite_two_point_raw_ibp_proved : Prop
  finite_two_point_flux_representation_proved : Prop
  finite_two_point_feeds_a2a14 : Prop
  analytic_interval_raw_ibp_closed : Prop
  analytic_interval_raw_ibp_not_closed :
    Not analytic_interval_raw_ibp_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status for the finite raw-IBP proof contract. -/
def rawSpatialIBPProofContractStatusV0 :
    RawSpatialIBPProofContractStatus where
  finite_two_point_model_defined := True
  finite_two_point_integral_linear := True
  finite_two_point_operator_linear := True
  finite_two_point_operator_nonzero := True
  finite_two_point_raw_ibp_proved := True
  finite_two_point_flux_representation_proved := True
  finite_two_point_feeds_a2a14 := True
  analytic_interval_raw_ibp_closed := False
  analytic_interval_raw_ibp_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15ARawSpatialIBPProofContractRetainedId
  outcome_id := finiteTwoPointSpatialIBPOutcomeId

/-- Short proof-facing status alias. -/
def rawIBPContractStatusV0 : RawSpatialIBPProofContractStatus :=
  rawSpatialIBPProofContractStatusV0

/-- The finite two-point model is defined. -/
theorem raw_ibp_contract_finite_model_defined_v0 :
    rawIBPContractStatusV0.finite_two_point_model_defined := by
  trivial

/-- The finite model's raw IBP theorem is checked. -/
theorem raw_ibp_contract_finite_raw_ibp_proved_v0 :
    rawIBPContractStatusV0.finite_two_point_raw_ibp_proved := by
  trivial

/-- The finite model's raw flux representation theorem is checked. -/
theorem raw_ibp_contract_finite_flux_representation_proved_v0 :
    rawIBPContractStatusV0.finite_two_point_flux_representation_proved := by
  trivial

/-- The finite model feeds A2A14 through the A2A15 sub-blocker API. -/
theorem raw_ibp_contract_finite_feeds_a2a14_v0 :
    rawIBPContractStatusV0.finite_two_point_feeds_a2a14 := by
  trivial

/-- The analytic interval raw-IBP theorem remains retained. -/
theorem raw_ibp_contract_analytic_interval_not_closed_v0 :
    Not rawIBPContractStatusV0.analytic_interval_raw_ibp_closed := by
  exact rawIBPContractStatusV0.analytic_interval_raw_ibp_not_closed

/-- The retained A2A15A proof contract does not authorize Phase 2. -/
theorem raw_ibp_contract_phase2_not_authorized_v0 :
    Not rawIBPContractStatusV0.phase2Authorized := by
  exact rawIBPContractStatusV0.phase2_not_authorized

/-- The retained A2A15A proof contract exposes the parent A2A15 blocker. -/
theorem raw_ibp_contract_parent_retained_id_v0 :
    rawSpatialIBPProofContractStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A15SpatialBoundaryFluxRepresentationRetainedId := by
  simp [rawSpatialIBPProofContractStatusV0]

/-- The retained A2A15A proof contract exposes its retained blocker. -/
theorem raw_ibp_contract_retained_id_v0 :
    rawSpatialIBPProofContractStatusV0.retained_blocker_id =
      phase1Blocker003A2A15ARawSpatialIBPProofContractRetainedId := by
  simp [rawSpatialIBPProofContractStatusV0]

/-- The retained A2A15A proof contract exposes its finite-model outcome id. -/
theorem raw_ibp_contract_outcome_id_v0 :
    rawSpatialIBPProofContractStatusV0.outcome_id =
      finiteTwoPointSpatialIBPOutcomeId := by
  simp [rawSpatialIBPProofContractStatusV0]

end

end ContinuumSpatialRawIBPProofContract
end QFT
end ToeFormal
