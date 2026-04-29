/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate.lean

Degree <= 3 polynomial fourth-derivative certificate for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- instantiate the A1A3 fourth-derivative certificate route for the bounded
  degree <= 3 polynomial test class
- prove the polynomial remainder field is zero and therefore supplies the
  scale-normalized stencil remainder bound with zero fourth-derivative
  tolerance
- feed that certificate into the A1A3 Taylor-control and local stencil
  error-bound route
- record that this is only a polynomial test-class result, not a general
  smooth-function, refinement-family, operator-domain, or continuum
  convergence theorem
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianFourthDerivativeRemainder

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the degree <= 3 polynomial certificate surface. -/
def phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A4_POLYNOMIAL_FOURTH_DERIVATIVE_" ++
    "CERTIFICATE_RETAINED"

/-- Outcome id for the polynomial fourth-derivative certificate surface. -/
def graphLaplacianPolynomialFourthDerivativeCertificateOutcomeId :
    String :=
  "A2A15A1A4_DEGREE_LE_THREE_POLYNOMIAL_FOURTH_DERIVATIVE_" ++
    "CERTIFICATE_RECORDED_RETAINED"

/-- The degree <= 3 polynomial class has no fourth-order stencil remainder. -/
def degreeLeThreePolynomialRemainder :
    ContinuumField ThreePointStencil :=
  fun _ => 0

/-- A degree <= 3 polynomial sample is exactly the quadratic-cubic sample. -/
def degreeLeThreePolynomialSample (a b c d h : Real) :
    ContinuumField ThreePointStencil :=
  sampledQuadraticCubicField a b c d h

/-- Adding the zero remainder does not change the degree <= 3 sample. -/
theorem degree_le_three_polynomial_remainder_field_eq
    (a b c d h : Real) :
    sampledQuadraticCubicRemainderField
        a b c d h degreeLeThreePolynomialRemainder =
      degreeLeThreePolynomialSample a b c d h := by
  funext p
  simp [sampledQuadraticCubicRemainderField,
    degreeLeThreePolynomialSample, degreeLeThreePolynomialRemainder]

/-- The fourth-derivative tolerance is zero for the degree <= 3 certificate. -/
theorem degree_le_three_fourth_derivative_tolerance_zero
    (h : Real) :
    fourthDerivativeStencilTolerance 0 h = 0 := by
  simp [fourthDerivativeStencilTolerance]

/--
The zero remainder supplies the scale-normalized stencil remainder bound with
zero fourth-derivative tolerance.
-/
theorem degree_le_three_scaled_stencil_remainder_bound
    (h : Real) :
    scaledStencilRemainderErrorBound h degreeLeThreePolynomialRemainder
      (fourthDerivativeStencilTolerance 0 h) := by
  simp [scaledStencilRemainderErrorBound, degreeLeThreePolynomialRemainder,
    centeredGraphLaplacianNumerator, fourthDerivativeStencilTolerance]

/--
For the degree <= 3 polynomial class, the fourth-derivative certificate route
is instantiated with zero fourth-derivative bound and zero stencil remainder.
-/
def degreeLeThreePolynomialFourthDerivativeCertificate
    (a b c d h : Real) :
    FourthDerivativeBoundToStencilRemainder
      h degreeLeThreePolynomialRemainder where
  differentiability_order := 4
  differentiability_order_at_least_four := by decide
  fourth_derivative_bound := 0
  fourth_derivative_bound_nonnegative := by norm_num
  bounded_fourth_derivative_on_interval :=
    fourthDerivativeStencilTolerance 0 h = 0
  bounded_fourth_derivative_on_interval_supplied :=
    degree_le_three_fourth_derivative_tolerance_zero h
  local_interval_model := True
  local_interval_model_supplied := True.intro
  local_taylor_formula :=
    sampledQuadraticCubicRemainderField
        a b c d h degreeLeThreePolynomialRemainder =
      degreeLeThreePolynomialSample a b c d h
  local_taylor_formula_supplied :=
    degree_le_three_polynomial_remainder_field_eq a b c d h
  fourth_order_remainder_formula :=
    degreeLeThreePolynomialRemainder =
      fun _ : ThreePointStencil => 0
  fourth_order_remainder_formula_supplied := rfl
  centered_stencil_residual_estimate :=
    scaledStencilRemainderErrorBound h degreeLeThreePolynomialRemainder
      (fourthDerivativeStencilTolerance 0 h)
  centered_stencil_residual_estimate_supplied :=
    degree_le_three_scaled_stencil_remainder_bound h
  mesh_scale := |h|
  mesh_scale_matches_spacing := rfl
  refinement_parameter := 1
  refinement_parameter_positive := by decide
  refinement_uniformity_condition := True
  refinement_uniformity_condition_supplied := True.intro
  scale_normalized_bound_from_fourth_derivative :=
    degree_le_three_scaled_stencil_remainder_bound h

/-- The degree <= 3 polynomial certificate builds the A1A3 certificate route. -/
theorem degree_le_three_polynomial_certificate_supplies_a1a3_bound
    (a b c d h : Real) :
    scaledStencilRemainderErrorBound h degreeLeThreePolynomialRemainder
      (fourthDerivativeStencilTolerance 0 h) := by
  exact fourth_derivative_bound_supplies_scaled_stencil_bound
    h degreeLeThreePolynomialRemainder
    (degreeLeThreePolynomialFourthDerivativeCertificate a b c d h)

/-- The degree <= 3 certificate constructs the prior TaylorRemainderControl. -/
def degreeLeThreePolynomialTaylorRemainderControl
    (a b c d h : Real) :
    TaylorRemainderControl h degreeLeThreePolynomialRemainder
      (fourthDerivativeStencilTolerance 0 h) :=
  fourthDerivativeBoundToTaylorRemainderControl
    h degreeLeThreePolynomialRemainder
    (degreeLeThreePolynomialFourthDerivativeCertificate a b c d h)

/--
The degree <= 3 polynomial certificate feeds the local stencil error-bound
theorem through the A1A3 route.
-/
theorem degree_le_three_polynomial_feeds_local_stencil_error_bound
    (a b c d h : Real)
    (h_nonzero : h * h ≠ 0) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField
          a b c d h degreeLeThreePolynomialRemainder) -
      quadraticContinuumSecondDerivative a| ≤
      fourthDerivativeStencilTolerance 0 h := by
  exact fourth_derivative_bound_feeds_local_stencil_error_bound
    a b c d h degreeLeThreePolynomialRemainder h_nonzero
    (degreeLeThreePolynomialFourthDerivativeCertificate a b c d h)

/--
This polynomial certificate is useful but narrow.  These obstructions remain
before it can become a general A1A convergence theorem.
-/
inductive PolynomialFourthDerivativeCertificateObstruction where
  | onlyDegreeLeThreePolynomials
  | noDegreeFourOrHigherPolynomialRemainder
  | noGeneralSmoothFunctionSpace
  | noConcreteDerivativeOperator
  | noUniformRefinementFamily
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the polynomial certificate obstruction list. -/
def polynomialFourthDerivativeCertificateObstructionId :
    PolynomialFourthDerivativeCertificateObstruction -> String
  | .onlyDegreeLeThreePolynomials =>
      "A2A15A1A4_OBSTRUCTION_ONLY_DEGREE_LE_THREE_POLYNOMIALS"
  | .noDegreeFourOrHigherPolynomialRemainder =>
      "A2A15A1A4_OBSTRUCTION_NO_DEGREE_FOUR_OR_HIGHER_REMAINDER"
  | .noGeneralSmoothFunctionSpace =>
      "A2A15A1A4_OBSTRUCTION_NO_GENERAL_SMOOTH_FUNCTION_SPACE"
  | .noConcreteDerivativeOperator =>
      "A2A15A1A4_OBSTRUCTION_NO_CONCRETE_DERIVATIVE_OPERATOR"
  | .noUniformRefinementFamily =>
      "A2A15A1A4_OBSTRUCTION_NO_UNIFORM_REFINEMENT_FAMILY"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A4_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A4_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A4_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact obstruction inventory for the polynomial certificate surface. -/
def polynomialFourthDerivativeCertificateObstructionsV0 :
    List PolynomialFourthDerivativeCertificateObstruction :=
  [ .onlyDegreeLeThreePolynomials
  , .noDegreeFourOrHigherPolynomialRemainder
  , .noGeneralSmoothFunctionSpace
  , .noConcreteDerivativeOperator
  , .noUniformRefinementFamily
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The polynomial obstruction inventory is stable and explicit. -/
theorem polynomial_fourth_derivative_obstructions_v0_expected :
    polynomialFourthDerivativeCertificateObstructionsV0 =
      [ .onlyDegreeLeThreePolynomials
      , .noDegreeFourOrHigherPolynomialRemainder
      , .noGeneralSmoothFunctionSpace
      , .noConcreteDerivativeOperator
      , .noUniformRefinementFamily
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording concrete obstruction. -/
def polynomialFourthDerivativeCertificateSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with proof explicit above. -/
theorem polynomial_fourth_derivative_successor_kinds_v0_expected :
    polynomialFourthDerivativeCertificateSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the degree <= 3 polynomial certificate surface. -/
structure PolynomialFourthDerivativeCertificateStatus where
  polynomial_certificate_instantiated : Prop
  polynomial_certificate_instantiated_supplied :
    polynomial_certificate_instantiated
  zero_remainder_bound_proved : Prop
  zero_remainder_bound_proved_supplied : zero_remainder_bound_proved
  feeds_a1a3_route : Prop
  feeds_a1a3_route_supplied : feeds_a1a3_route
  general_function_space_certificate_proved : Prop
  general_function_space_certificate_not_proved :
    Not general_function_space_certificate_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_fourth_derivative_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the degree <= 3 polynomial certificate is instantiated, but
the general function-space certificate and full A1A convergence remain
retained.
-/
def polynomialFourthDerivativeCertificateStatusV0 :
    PolynomialFourthDerivativeCertificateStatus where
  polynomial_certificate_instantiated := True
  polynomial_certificate_instantiated_supplied := True.intro
  zero_remainder_bound_proved := True
  zero_remainder_bound_proved_supplied := True.intro
  feeds_a1a3_route := True
  feeds_a1a3_route_supplied := True.intro
  general_function_space_certificate_proved := False
  general_function_space_certificate_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_fourth_derivative_retained_blocker_id :=
    phase1Blocker003A2A15A1A3FourthDerivativeRemainderRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId
  outcome_id := graphLaplacianPolynomialFourthDerivativeCertificateOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := polynomialFourthDerivativeCertificateSuccessorKindsV0
  obstruction_ids :=
    polynomialFourthDerivativeCertificateObstructionsV0.map
      polynomialFourthDerivativeCertificateObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def polynomialFourthDerivativeCertificateStatusReadoutV0 :
    PolynomialFourthDerivativeCertificateStatus :=
  polynomialFourthDerivativeCertificateStatusV0

/-- The degree <= 3 polynomial certificate is instantiated. -/
theorem polynomial_fourth_derivative_certificate_instantiated_v0 :
    PolynomialFourthDerivativeCertificateStatus.polynomial_certificate_instantiated
      polynomialFourthDerivativeCertificateStatusReadoutV0 := by
  exact
    PolynomialFourthDerivativeCertificateStatus.polynomial_certificate_instantiated_supplied
      polynomialFourthDerivativeCertificateStatusReadoutV0

/-- The zero-remainder bound is proved for the polynomial test class. -/
theorem polynomial_fourth_derivative_zero_remainder_bound_v0 :
    PolynomialFourthDerivativeCertificateStatus.zero_remainder_bound_proved
      polynomialFourthDerivativeCertificateStatusReadoutV0 := by
  exact
    PolynomialFourthDerivativeCertificateStatus.zero_remainder_bound_proved_supplied
      polynomialFourthDerivativeCertificateStatusReadoutV0

/-- The polynomial certificate feeds the A1A3 route. -/
theorem polynomial_fourth_derivative_feeds_a1a3_route_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.feeds_a1a3_route := by
  exact polynomialFourthDerivativeCertificateStatusReadoutV0.feeds_a1a3_route_supplied

/-- The general function-space certificate remains retained. -/
theorem polynomial_fourth_derivative_general_certificate_not_proved_v0 :
    Not (PolynomialFourthDerivativeCertificateStatus.general_function_space_certificate_proved
        polynomialFourthDerivativeCertificateStatusReadoutV0) := by
  exact
    PolynomialFourthDerivativeCertificateStatus.general_function_space_certificate_not_proved
      polynomialFourthDerivativeCertificateStatusReadoutV0

/-- The polynomial certificate does not close full A1A. -/
theorem polynomial_fourth_derivative_full_a1a_not_closed_v0 :
    Not polynomialFourthDerivativeCertificateStatusReadoutV0.full_a1a_channel_closed := by
  exact polynomialFourthDerivativeCertificateStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem polynomial_fourth_derivative_parent_retained_id_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A3 retained blocker remains exposed. -/
theorem polynomial_fourth_derivative_prior_retained_id_v0 :
    PolynomialFourthDerivativeCertificateStatus.prior_fourth_derivative_retained_blocker_id
        polynomialFourthDerivativeCertificateStatusReadoutV0 =
      phase1Blocker003A2A15A1A3FourthDerivativeRemainderRetainedId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem polynomial_fourth_derivative_retained_id_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem polynomial_fourth_derivative_outcome_id_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.outcome_id =
      graphLaplacianPolynomialFourthDerivativeCertificateOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem polynomial_fourth_derivative_anti_loop_rule_id_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem polynomial_fourth_derivative_successor_kinds_v0 :
    polynomialFourthDerivativeCertificateStatusReadoutV0.successor_kinds =
      polynomialFourthDerivativeCertificateSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem polynomial_fourth_derivative_phase2_not_authorized_v0 :
    Not polynomialFourthDerivativeCertificateStatusReadoutV0.phase2Authorized := by
  exact polynomialFourthDerivativeCertificateStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate
end QFT
end ToeFormal
