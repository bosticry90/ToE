/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianPolynomialTestClassCapstone.lean

Capstone/readout for the polynomial test-class branch of the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- record that the degree <= 3 zero-remainder polynomial certificate is handled
- record that the degree <= 4 bounded quartic-remainder certificate is handled
- expose the local stencil error-bound route for those polynomial test classes
- cap the polynomial subclass branch and retain the general smooth Taylor,
  refinement/uniform-convergence, function-space, operator-domain, and
  continuum-convergence obligations
- keep Phase 2 authorization, full A1A closure, seam closure, empirical
  validation, and master-action promotion out of scope
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianBoundedQuarticPolynomialRemainder

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianPolynomialTestClassCapstone

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianPolynomialFourthDerivativeCertificate
open ContinuumSpatialGraphLaplacianBoundedQuarticPolynomialRemainder

set_option autoImplicit false

noncomputable section

/-- Machine-facing id for the polynomial test-class capstone surface. -/
def graphLaplacianPolynomialTestClassCapstoneId : String :=
  "A2A15A1A_POLYNOMIAL_TEST_CLASS_CAPSTONE"

/-- Retained blocker after the polynomial test-class capstone. -/
def phase1Blocker003A2A15A1APolynomialTestClassCapstoneRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A_POLYNOMIAL_TEST_CLASS_" ++
    "CAPSTONE_GENERAL_SMOOTH_CONVERGENCE_RETAINED"

/-- Outcome id for the polynomial test-class capstone. -/
def graphLaplacianPolynomialTestClassCapstoneOutcomeId : String :=
  "POLYNOMIAL_TEST_CLASS_STENCIL_CONSISTENCY_DISCHARGED_" ++
    "GENERAL_SMOOTH_CONVERGENCE_RETAINED"

/-- The degree <= 3 branch still exposes its zero-remainder theorem. -/
theorem polynomial_test_class_degree_le_three_zero_remainder_bound
    (h : Real) :
    scaledStencilRemainderErrorBound h degreeLeThreePolynomialRemainder
      (fourthDerivativeStencilTolerance 0 h) := by
  exact degree_le_three_scaled_stencil_remainder_bound h

/-- The degree <= 4 branch still exposes its bounded quartic-remainder theorem. -/
theorem polynomial_test_class_degree_le_four_remainder_bound
    (e h : Real) :
    scaledStencilRemainderErrorBound h
      (boundedQuarticPolynomialRemainder e h)
      (fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h) := by
  exact bounded_quartic_scaled_stencil_remainder_bound e h

/-- Degree <= 3 polynomial samples have the local A1A stencil error route. -/
theorem polynomial_test_class_degree_le_three_local_error_route
    (a b c d h : Real)
    (h_nonzero : h * h ≠ 0) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField
          a b c d h degreeLeThreePolynomialRemainder) -
      quadraticContinuumSecondDerivative a| ≤
      fourthDerivativeStencilTolerance 0 h := by
  exact degree_le_three_polynomial_feeds_local_stencil_error_bound
    a b c d h h_nonzero

/-- Degree <= 4 polynomial samples have the local A1A stencil error route. -/
theorem polynomial_test_class_degree_le_four_local_error_route
    (a b c d e h : Real)
    (h_nonzero : h * h ≠ 0) :
    |centeredScaledGraphLaplacianAtCenter h
        (degreeLeFourPolynomialSample a b c d e h) -
      quadraticContinuumSecondDerivative a| ≤
      fourthDerivativeStencilTolerance
        (boundedQuarticFourthDerivativeBound e) h := by
  exact bounded_quartic_polynomial_feeds_local_stencil_error_bound
    a b c d e h h_nonzero

/--
The polynomial branch is capped here.  These obstructions are exactly what
separates local polynomial consistency from general A1A convergence.
-/
inductive PolynomialTestClassCapstoneObstruction where
  | noGeneralSmoothTaylorTheorem
  | noUniformRefinementConvergence
  | noGeneralFunctionSpaceSemantics
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the polynomial capstone obstruction list. -/
def polynomialTestClassCapstoneObstructionId :
    PolynomialTestClassCapstoneObstruction -> String
  | .noGeneralSmoothTaylorTheorem =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_GENERAL_SMOOTH_TAYLOR_THEOREM"
  | .noUniformRefinementConvergence =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_UNIFORM_REFINEMENT_CONVERGENCE"
  | .noGeneralFunctionSpaceSemantics =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_GENERAL_FUNCTION_SPACE_SEMANTICS"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A_POLYNOMIAL_CAPSTONE_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the capped polynomial test-class branch. -/
def polynomialTestClassCapstoneObstructionsV0 :
    List PolynomialTestClassCapstoneObstruction :=
  [ .noGeneralSmoothTaylorTheorem
  , .noUniformRefinementConvergence
  , .noGeneralFunctionSpaceSemantics
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The capstone obstruction inventory is stable and explicit. -/
theorem polynomial_test_class_capstone_obstructions_v0_expected :
    polynomialTestClassCapstoneObstructionsV0 =
      [ .noGeneralSmoothTaylorTheorem
      , .noUniformRefinementConvergence
      , .noGeneralFunctionSpaceSemantics
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- The capstone satisfies the anti-loop rule by recording concrete obstruction. -/
def polynomialTestClassCapstoneSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with local proofs above. -/
theorem polynomial_test_class_capstone_successor_kinds_v0_expected :
    polynomialTestClassCapstoneSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the polynomial test-class capstone. -/
structure PolynomialTestClassCapstoneStatus where
  capstone_recorded : Prop
  capstone_recorded_supplied : capstone_recorded
  degree_le_three_zero_remainder_handled : Prop
  degree_le_three_zero_remainder_handled_supplied :
    degree_le_three_zero_remainder_handled
  degree_le_four_bounded_remainder_handled : Prop
  degree_le_four_bounded_remainder_handled_supplied :
    degree_le_four_bounded_remainder_handled
  local_polynomial_stencil_error_route_available : Prop
  local_polynomial_stencil_error_route_available_supplied :
    local_polynomial_stencil_error_route_available
  general_smooth_taylor_theorem_proved : Prop
  general_smooth_taylor_theorem_not_proved :
    Not general_smooth_taylor_theorem_proved
  uniform_refinement_convergence_proved : Prop
  uniform_refinement_convergence_not_proved :
    Not uniform_refinement_convergence_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  degree_le_three_retained_blocker_id : String
  degree_le_four_retained_blocker_id : String
  retained_blocker_id : String
  capstone_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the polynomial test-class branch is capped, while general
smooth Taylor control and refinement/uniform convergence remain retained.
-/
def polynomialTestClassCapstoneStatusV0 :
    PolynomialTestClassCapstoneStatus where
  capstone_recorded := True
  capstone_recorded_supplied := True.intro
  degree_le_three_zero_remainder_handled := True
  degree_le_three_zero_remainder_handled_supplied := True.intro
  degree_le_four_bounded_remainder_handled := True
  degree_le_four_bounded_remainder_handled_supplied := True.intro
  local_polynomial_stencil_error_route_available := True
  local_polynomial_stencil_error_route_available_supplied := True.intro
  general_smooth_taylor_theorem_proved := False
  general_smooth_taylor_theorem_not_proved := by
    intro h
    exact h
  uniform_refinement_convergence_proved := False
  uniform_refinement_convergence_not_proved := by
    intro h
    exact h
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  degree_le_three_retained_blocker_id :=
    phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId
  degree_le_four_retained_blocker_id :=
    phase1Blocker003A2A15A1A5BoundedFourthDegreePolynomialRemainderRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A15A1APolynomialTestClassCapstoneRetainedId
  capstone_id := graphLaplacianPolynomialTestClassCapstoneId
  outcome_id := graphLaplacianPolynomialTestClassCapstoneOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := polynomialTestClassCapstoneSuccessorKindsV0
  obstruction_ids :=
    polynomialTestClassCapstoneObstructionsV0.map
      polynomialTestClassCapstoneObstructionId
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def polynomialTestClassCapstoneStatusReadoutV0 :
    PolynomialTestClassCapstoneStatus :=
  polynomialTestClassCapstoneStatusV0

/-- The polynomial test-class capstone is recorded. -/
theorem polynomial_test_class_capstone_recorded_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.capstone_recorded := by
  exact polynomialTestClassCapstoneStatusReadoutV0.capstone_recorded_supplied

/-- Degree <= 3 zero-remainder polynomial samples are handled. -/
theorem polynomial_test_class_degree_le_three_handled_v0 :
    PolynomialTestClassCapstoneStatus.degree_le_three_zero_remainder_handled
      polynomialTestClassCapstoneStatusReadoutV0 := by
  exact
    PolynomialTestClassCapstoneStatus.degree_le_three_zero_remainder_handled_supplied
      polynomialTestClassCapstoneStatusReadoutV0

/-- Degree <= 4 bounded-remainder polynomial samples are handled. -/
theorem polynomial_test_class_degree_le_four_handled_v0 :
    PolynomialTestClassCapstoneStatus.degree_le_four_bounded_remainder_handled
      polynomialTestClassCapstoneStatusReadoutV0 := by
  exact
    PolynomialTestClassCapstoneStatus.degree_le_four_bounded_remainder_handled_supplied
      polynomialTestClassCapstoneStatusReadoutV0

/-- The local polynomial stencil error route is available. -/
theorem polynomial_test_class_local_route_available_v0 :
    PolynomialTestClassCapstoneStatus.local_polynomial_stencil_error_route_available
      polynomialTestClassCapstoneStatusReadoutV0 := by
  exact
    PolynomialTestClassCapstoneStatus.local_polynomial_stencil_error_route_available_supplied
      polynomialTestClassCapstoneStatusReadoutV0

/-- The general smooth Taylor theorem remains retained. -/
theorem polynomial_test_class_general_smooth_taylor_not_proved_v0 :
    Not (PolynomialTestClassCapstoneStatus.general_smooth_taylor_theorem_proved
      polynomialTestClassCapstoneStatusReadoutV0) := by
  exact
    PolynomialTestClassCapstoneStatus.general_smooth_taylor_theorem_not_proved
      polynomialTestClassCapstoneStatusReadoutV0

/-- Uniform refinement convergence remains retained. -/
theorem polynomial_test_class_uniform_refinement_not_proved_v0 :
    Not (PolynomialTestClassCapstoneStatus.uniform_refinement_convergence_proved
      polynomialTestClassCapstoneStatusReadoutV0) := by
  exact
    PolynomialTestClassCapstoneStatus.uniform_refinement_convergence_not_proved
      polynomialTestClassCapstoneStatusReadoutV0

/-- The polynomial capstone does not close full A1A. -/
theorem polynomial_test_class_full_a1a_not_closed_v0 :
    Not polynomialTestClassCapstoneStatusReadoutV0.full_a1a_channel_closed := by
  exact polynomialTestClassCapstoneStatusReadoutV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem polynomial_test_class_parent_retained_id_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The capstone exposes the A1A4 retained blocker id. -/
theorem polynomial_test_class_degree_le_three_retained_id_v0 :
    PolynomialTestClassCapstoneStatus.degree_le_three_retained_blocker_id
        polynomialTestClassCapstoneStatusReadoutV0 =
      phase1Blocker003A2A15A1A4PolynomialFourthDerivativeCertificateRetainedId := by
  rfl

/-- The capstone exposes the A1A5 retained blocker id. -/
theorem polynomial_test_class_degree_le_four_retained_id_v0 :
    PolynomialTestClassCapstoneStatus.degree_le_four_retained_blocker_id
        polynomialTestClassCapstoneStatusReadoutV0 =
      phase1Blocker003A2A15A1A5BoundedFourthDegreePolynomialRemainderRetainedId := by
  rfl

/-- The theorem-facing capstone exposes its retained blocker id. -/
theorem polynomial_test_class_capstone_retained_id_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.retained_blocker_id =
      phase1Blocker003A2A15A1APolynomialTestClassCapstoneRetainedId := by
  rfl

/-- The theorem-facing capstone exposes its capstone id. -/
theorem polynomial_test_class_capstone_id_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.capstone_id =
      graphLaplacianPolynomialTestClassCapstoneId := by
  rfl

/-- The theorem-facing capstone exposes its outcome id. -/
theorem polynomial_test_class_capstone_outcome_id_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.outcome_id =
      graphLaplacianPolynomialTestClassCapstoneOutcomeId := by
  rfl

/-- The capstone is governed by the post-capstone anti-loop rule. -/
theorem polynomial_test_class_capstone_anti_loop_rule_id_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem polynomial_test_class_capstone_successor_kinds_v0 :
    polynomialTestClassCapstoneStatusReadoutV0.successor_kinds =
      polynomialTestClassCapstoneSuccessorKindsV0 := by
  rfl

/-- Phase 2 remains unauthorized after this capstone/readout. -/
theorem polynomial_test_class_capstone_phase2_not_authorized_v0 :
    Not polynomialTestClassCapstoneStatusReadoutV0.phase2Authorized := by
  exact polynomialTestClassCapstoneStatusReadoutV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianPolynomialTestClassCapstone
end QFT
end ToeFormal
