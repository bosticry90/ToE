/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianBoundedQuarticPolynomialRemainder.lean

Degree <= 4 polynomial remainder certificate for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- extend the degree <= 3 zero-remainder polynomial test class to a bounded
  quartic polynomial remainder on the same three-point stencil
- prove the nonzero quartic remainder numerator and its scale-normalized
  bound from the polynomial fourth-derivative bound `24 * |e|`
- feed that certificate into the existing A1A3 fourth-derivative and
  Taylor-control route
- record that this is still only a polynomial test-class result, not a
  general smooth-function, refinement-family, operator-domain, or continuum
  convergence theorem
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianBoundedQuarticPolynomialRemainder

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the bounded quartic polynomial remainder surface. -/
def phase1Blocker003A2A15A1A5BoundedFourthDegreePolynomialRemainderRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A5_BOUNDED_FOURTH_DEGREE_" ++
    "POLYNOMIAL_REMAINDER_RETAINED"

/-- Outcome id for the bounded quartic polynomial remainder surface. -/
def graphLaplacianBoundedQuarticPolynomialRemainderOutcomeId :
    String :=
  "A2A15A1A5_BOUNDED_FOURTH_DEGREE_POLYNOMIAL_REMAINDER_" ++
    "BOUND_RECORDED_RETAINED"

/-- The quartic remainder for a degree <= 4 polynomial sample. -/
def boundedQuarticPolynomialRemainder (e h : Real) :
    ContinuumField ThreePointStencil :=
  fun p =>
    let x := threePointCoordinate h p
    e * x * x * x * x

/-- A degree <= 4 sample is quadratic plus odd cubic plus quartic remainder. -/
def degreeLeFourPolynomialSample (a b c d e h : Real) :
    ContinuumField ThreePointStencil :=
  sampledQuadraticCubicRemainderField
    a b c d h (boundedQuarticPolynomialRemainder e h)

/-- The quartic sample expands to the expected degree <= 4 polynomial. -/
theorem degree_le_four_polynomial_sample_expands
    (a b c d e h : Real) :
    degreeLeFourPolynomialSample a b c d e h =
      fun p =>
        let x := threePointCoordinate h p
        a * x * x + b * x + c + d * x * x * x +
          e * x * x * x * x := by
  funext p
  simp [degreeLeFourPolynomialSample,
    sampledQuadraticCubicRemainderField, sampledQuadraticCubicField,
    boundedQuarticPolynomialRemainder]

/-- The centered numerator of the quartic remainder is nonzero in general. -/
theorem bounded_quartic_remainder_numerator_exact
    (e h : Real) :
    centeredGraphLaplacianNumerator
        (boundedQuarticPolynomialRemainder e h) =
      2 * e * h * h * h * h := by
  simp [centeredGraphLaplacianNumerator,
    boundedQuarticPolynomialRemainder, threePointCoordinate]
  ring

/-- The scaled quartic remainder is `2 * e * h^2` on this stencil. -/
theorem bounded_quartic_remainder_scaled_exact
    (e h : Real) :
    centeredGraphLaplacianNumerator
        (boundedQuarticPolynomialRemainder e h) / (h * h) =
      2 * e * (h * h) := by
  rw [bounded_quartic_remainder_numerator_exact]
  field_simp

/-- The fourth-derivative bound for `e * x^4` is represented as `24 * |e|`. -/
def boundedQuarticFourthDerivativeBound (e : Real) : Real :=
  24 * |e|

/-- The quartic polynomial fourth-derivative bound is nonnegative. -/
theorem bounded_quartic_fourth_derivative_bound_nonnegative
    (e : Real) :
    0 ≤ boundedQuarticFourthDerivativeBound e := by
  unfold boundedQuarticFourthDerivativeBound
  nlinarith [abs_nonneg e]

/-- The A1A3 tolerance for a quartic bound is `2 * |e| * h^2`. -/
theorem bounded_quartic_fourth_derivative_tolerance_eq
    (e h : Real) :
    fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h =
      2 * |e| * (h * h) := by
  simp [boundedQuarticFourthDerivativeBound,
    fourthDerivativeStencilTolerance]
  ring

/--
The quartic remainder supplies the scale-normalized stencil remainder bound
from the polynomial fourth-derivative bound `24 * |e|`.
-/
theorem bounded_quartic_scaled_stencil_remainder_bound
    (e h : Real) :
    scaledStencilRemainderErrorBound h
      (boundedQuarticPolynomialRemainder e h)
      (fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h) := by
  by_cases h_zero : h = 0
  · simp [scaledStencilRemainderErrorBound,
      boundedQuarticPolynomialRemainder, centeredGraphLaplacianNumerator,
      threePointCoordinate, fourthDerivativeStencilTolerance,
      boundedQuarticFourthDerivativeBound, h_zero]
  · unfold scaledStencilRemainderErrorBound
    rw [bounded_quartic_remainder_scaled_exact e h]
    have hsq_nonneg : 0 ≤ h * h := mul_self_nonneg h
    calc
      |2 * e * (h * h)| = 2 * |e| * (h * h) := by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : 0 ≤ (2 : Real)),
          abs_of_nonneg hsq_nonneg]
      _ ≤ fourthDerivativeStencilTolerance
          (boundedQuarticFourthDerivativeBound e) h := by
        exact le_of_eq
          (bounded_quartic_fourth_derivative_tolerance_eq e h).symm

/--
For degree <= 4 polynomial samples, the A1A3 fourth-derivative certificate
route is instantiated with the explicit quartic remainder and bound
`24 * |e|`.
-/
def boundedQuarticPolynomialFourthDerivativeCertificate
    (a b c d e h : Real) :
    FourthDerivativeBoundToStencilRemainder
      h (boundedQuarticPolynomialRemainder e h) where
  differentiability_order := 4
  differentiability_order_at_least_four := by decide
  fourth_derivative_bound := boundedQuarticFourthDerivativeBound e
  fourth_derivative_bound_nonnegative :=
    bounded_quartic_fourth_derivative_bound_nonnegative e
  bounded_fourth_derivative_on_interval :=
    fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h =
      2 * |e| * (h * h)
  bounded_fourth_derivative_on_interval_supplied :=
    bounded_quartic_fourth_derivative_tolerance_eq e h
  local_interval_model := True
  local_interval_model_supplied := True.intro
  local_taylor_formula :=
    degreeLeFourPolynomialSample a b c d e h =
      fun p =>
        let x := threePointCoordinate h p
        a * x * x + b * x + c + d * x * x * x +
          e * x * x * x * x
  local_taylor_formula_supplied :=
    degree_le_four_polynomial_sample_expands a b c d e h
  fourth_order_remainder_formula :=
    boundedQuarticPolynomialRemainder e h =
      fun p =>
        let x := threePointCoordinate h p
        e * x * x * x * x
  fourth_order_remainder_formula_supplied := rfl
  centered_stencil_residual_estimate :=
    scaledStencilRemainderErrorBound h
      (boundedQuarticPolynomialRemainder e h)
      (fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h)
  centered_stencil_residual_estimate_supplied :=
    bounded_quartic_scaled_stencil_remainder_bound e h
  mesh_scale := |h|
  mesh_scale_matches_spacing := rfl
  refinement_parameter := 1
  refinement_parameter_positive := by decide
  refinement_uniformity_condition := True
  refinement_uniformity_condition_supplied := True.intro
  scale_normalized_bound_from_fourth_derivative :=
    bounded_quartic_scaled_stencil_remainder_bound e h

/-- The bounded quartic certificate supplies the A1A3 scaled bound. -/
theorem bounded_quartic_polynomial_certificate_supplies_a1a3_bound
    (a b c d e h : Real) :
    scaledStencilRemainderErrorBound h
      (boundedQuarticPolynomialRemainder e h)
      (fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h) := by
  exact fourth_derivative_bound_supplies_scaled_stencil_bound
    h (boundedQuarticPolynomialRemainder e h)
    (boundedQuarticPolynomialFourthDerivativeCertificate a b c d e h)

/-- The bounded quartic certificate constructs the prior TaylorRemainderControl. -/
def boundedQuarticPolynomialTaylorRemainderControl
    (a b c d e h : Real) :
    TaylorRemainderControl h
      (boundedQuarticPolynomialRemainder e h)
      (fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h) :=
  fourthDerivativeBoundToTaylorRemainderControl
    h (boundedQuarticPolynomialRemainder e h)
    (boundedQuarticPolynomialFourthDerivativeCertificate a b c d e h)

/--
The bounded quartic polynomial certificate feeds the local stencil error-bound
theorem through the A1A3 route.
-/
theorem bounded_quartic_polynomial_feeds_local_stencil_error_bound
    (a b c d e h : Real)
    (h_nonzero : h * h ≠ 0) :
    |centeredScaledGraphLaplacianAtCenter h
        (degreeLeFourPolynomialSample a b c d e h) -
      quadraticContinuumSecondDerivative a| ≤
      fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h := by
  exact fourth_derivative_bound_feeds_local_stencil_error_bound
    a b c d h (boundedQuarticPolynomialRemainder e h) h_nonzero
    (boundedQuarticPolynomialFourthDerivativeCertificate a b c d e h)

/--
This quartic polynomial certificate exposes a nonzero remainder bound but is
still a finite polynomial test-class result, not a general A1A theorem.
-/
inductive BoundedQuarticPolynomialRemainderObstruction where
  | onlyDegreeLeFourPolynomials
  | noDegreeFiveOrHigherRemainder
  | noGeneralSmoothFunctionSpace
  | noConcreteDerivativeOperator
  | noUniformRefinementFamily
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the bounded quartic obstruction list. -/
def boundedQuarticPolynomialRemainderObstructionId :
    BoundedQuarticPolynomialRemainderObstruction -> String
  | .onlyDegreeLeFourPolynomials =>
      "A2A15A1A5_OBSTRUCTION_ONLY_DEGREE_LE_FOUR_POLYNOMIALS"
  | .noDegreeFiveOrHigherRemainder =>
      "A2A15A1A5_OBSTRUCTION_NO_DEGREE_FIVE_OR_HIGHER_REMAINDER"
  | .noGeneralSmoothFunctionSpace =>
      "A2A15A1A5_OBSTRUCTION_NO_GENERAL_SMOOTH_FUNCTION_SPACE"
  | .noConcreteDerivativeOperator =>
      "A2A15A1A5_OBSTRUCTION_NO_CONCRETE_DERIVATIVE_OPERATOR"
  | .noUniformRefinementFamily =>
      "A2A15A1A5_OBSTRUCTION_NO_UNIFORM_REFINEMENT_FAMILY"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A5_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A5_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A5_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"

/-- Exact obstruction inventory for the bounded quartic surface. -/
def boundedQuarticPolynomialRemainderObstructionsV0 :
    List BoundedQuarticPolynomialRemainderObstruction :=
  [ .onlyDegreeLeFourPolynomials
  , .noDegreeFiveOrHigherRemainder
  , .noGeneralSmoothFunctionSpace
  , .noConcreteDerivativeOperator
  , .noUniformRefinementFamily
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  ]

/-- The bounded quartic obstruction inventory is stable and explicit. -/
theorem bounded_quartic_polynomial_obstructions_v0_expected :
    boundedQuarticPolynomialRemainderObstructionsV0 =
      [ .onlyDegreeLeFourPolynomials
      , .noDegreeFiveOrHigherRemainder
      , .noGeneralSmoothFunctionSpace
      , .noConcreteDerivativeOperator
      , .noUniformRefinementFamily
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      ] := by
  rfl

/-- This successor satisfies the anti-loop rule by recording concrete obstruction. -/
def boundedQuarticPolynomialRemainderSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with local proof explicit above. -/
theorem bounded_quartic_polynomial_successor_kinds_v0_expected :
    boundedQuarticPolynomialRemainderSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the degree <= 4 bounded quartic remainder surface. -/
structure BoundedQuarticPolynomialRemainderStatus where
  quartic_remainder_exposed : Prop
  quartic_remainder_exposed_supplied : quartic_remainder_exposed
  bounded_fourth_degree_certificate_instantiated : Prop
  bounded_fourth_degree_certificate_instantiated_supplied :
    bounded_fourth_degree_certificate_instantiated
  nonzero_remainder_bound_proved : Prop
  nonzero_remainder_bound_proved_supplied : nonzero_remainder_bound_proved
  feeds_a1a3_route : Prop
  feeds_a1a3_route_supplied : feeds_a1a3_route
  general_function_space_certificate_proved : Prop
  general_function_space_certificate_not_proved :
    Not general_function_space_certificate_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_polynomial_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: degree <= 4 polynomial remainders are handled locally, but the
general function-space certificate and full A1A convergence remain retained.
-/
def boundedQuarticPolynomialRemainderStatusV0 :
    BoundedQuarticPolynomialRemainderStatus where
  quartic_remainder_exposed := True
  quartic_remainder_exposed_supplied := True.intro
  bounded_fourth_degree_certificate_instantiated := True
  bounded_fourth_degree_certificate_instantiated_supplied := True.intro
  nonzero_remainder_bound_proved := True
  nonzero_remainder_bound_proved_supplied := True.intro
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
  prior_polynomial_retained_blocker_id :=
    phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1A5BoundedFourthDegreePolynomialRemainderRetainedId
  outcome_id := graphLaplacianBoundedQuarticPolynomialRemainderOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := boundedQuarticPolynomialRemainderSuccessorKindsV0
  obstruction_ids :=
    boundedQuarticPolynomialRemainderObstructionsV0.map
      boundedQuarticPolynomialRemainderObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def boundedQuarticPolynomialRemainderStatusReadoutV0 :
    BoundedQuarticPolynomialRemainderStatus :=
  boundedQuarticPolynomialRemainderStatusV0

/-- The quartic remainder is explicitly exposed. -/
theorem bounded_quartic_polynomial_remainder_exposed_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.quartic_remainder_exposed := by
  exact
    boundedQuarticPolynomialRemainderStatusReadoutV0.quartic_remainder_exposed_supplied

/-- The bounded degree-four certificate is instantiated. -/
theorem bounded_quartic_polynomial_certificate_instantiated_v0 :
    BoundedQuarticPolynomialRemainderStatus.bounded_fourth_degree_certificate_instantiated
          boundedQuarticPolynomialRemainderStatusReadoutV0 := by
  exact
    BoundedQuarticPolynomialRemainderStatus.bounded_fourth_degree_certificate_instantiated_supplied
          boundedQuarticPolynomialRemainderStatusReadoutV0

/-- The nonzero quartic remainder bound is proved locally. -/
theorem bounded_quartic_polynomial_remainder_bound_proved_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.nonzero_remainder_bound_proved := by
  exact
    BoundedQuarticPolynomialRemainderStatus.nonzero_remainder_bound_proved_supplied
      boundedQuarticPolynomialRemainderStatusReadoutV0

/-- The bounded quartic certificate feeds the A1A3 route. -/
theorem bounded_quartic_polynomial_feeds_a1a3_route_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.feeds_a1a3_route := by
  exact
    boundedQuarticPolynomialRemainderStatusReadoutV0.feeds_a1a3_route_supplied

/-- The general function-space certificate remains retained. -/
theorem bounded_quartic_polynomial_general_certificate_not_proved_v0 :
    Not (BoundedQuarticPolynomialRemainderStatus.general_function_space_certificate_proved
      boundedQuarticPolynomialRemainderStatusReadoutV0) := by
  exact
    boundedQuarticPolynomialRemainderStatusReadoutV0.general_function_space_certificate_not_proved

/-- The bounded quartic surface does not close full A1A. -/
theorem bounded_quartic_polynomial_full_a1a_not_closed_v0 :
    Not boundedQuarticPolynomialRemainderStatusReadoutV0.full_a1a_channel_closed := by
  exact boundedQuarticPolynomialRemainderStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem bounded_quartic_polynomial_parent_retained_id_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A4 retained blocker remains exposed. -/
theorem bounded_quartic_polynomial_prior_retained_id_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.prior_polynomial_retained_blocker_id =
      phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId := by
  rfl

/-- The theorem-facing surface exposes its retained blocker id. -/
theorem bounded_quartic_polynomial_retained_id_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1A5BoundedFourthDegreePolynomialRemainderRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem bounded_quartic_polynomial_outcome_id_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.outcome_id =
      graphLaplacianBoundedQuarticPolynomialRemainderOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem bounded_quartic_polynomial_anti_loop_rule_id_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem bounded_quartic_polynomial_successor_kinds_v0 :
    boundedQuarticPolynomialRemainderStatusReadoutV0.successor_kinds =
      boundedQuarticPolynomialRemainderSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this theorem-facing A1A attempt. -/
theorem bounded_quartic_polynomial_phase2_not_authorized_v0 :
    Not boundedQuarticPolynomialRemainderStatusReadoutV0.phase2Authorized := by
  exact boundedQuarticPolynomialRemainderStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianBoundedQuarticPolynomialRemainder
end QFT
end ToeFormal
