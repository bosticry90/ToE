/-
ToeFormal/QFT/ContinuumGreenIdentityAttempt.lean

Bounded discharge attempt for PHASE1-BLOCKER-003A.

Scope:
- define the selected scalar kinetic operator/function-space pair more
  concretely than the retained Green-identity surface
- state the scalar kinetic Green identity over that pair
- prove that a supplied concrete assumption bundle yields the retained
  Green-identity object and the existing integration-by-parts route
- record the precise next retained sub-blockers when the current formal model
  does not yet supply concrete differentiable-function analysis
- no unconditional Green-identity discharge
- no operator-domain, residual-separation, or Phase 2 authorization claim
-/

import ToeFormal.QFT.ContinuumGreenIdentityRetained

namespace ToeFormal
namespace QFT
namespace ContinuumGreenIdentityAttempt

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
set_option autoImplicit false

noncomputable section

/-- Next retained sub-blockers exposed by the 003A discharge attempt. -/
inductive Phase1Blocker003AGreenIdentitySubBlocker where
  | concreteDifferentiableFunctionSpace
  | closedBoundaryUniverse
  | integrationRegularity
  | operatorDomainClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained 003A sub-blockers. -/
def phase1Blocker003AGreenIdentitySubBlockerId :
    Phase1Blocker003AGreenIdentitySubBlocker → String
  | .concreteDifferentiableFunctionSpace =>
      "PHASE1-BLOCKER-003A1_DIFFERENTIABLE_FUNCTION_SPACE_RETAINED"
  | .closedBoundaryUniverse =>
      "PHASE1-BLOCKER-003A2_CLOSED_BOUNDARY_UNIVERSE_RETAINED"
  | .integrationRegularity =>
      "PHASE1-BLOCKER-003A3_INTEGRATION_REGULARITY_RETAINED"
  | .operatorDomainClosure =>
      "PHASE1-BLOCKER-003A4_OPERATOR_DOMAIN_CLOSURE_RETAINED"

/-- Current retained sub-blockers for the selected scalar kinetic Green identity. -/
def phase1Blocker003AGreenIdentitySubBlockersV1 :
    List Phase1Blocker003AGreenIdentitySubBlocker :=
  [ Phase1Blocker003AGreenIdentitySubBlocker.concreteDifferentiableFunctionSpace
  , Phase1Blocker003AGreenIdentitySubBlocker.closedBoundaryUniverse
  , Phase1Blocker003AGreenIdentitySubBlocker.integrationRegularity
  , Phase1Blocker003AGreenIdentitySubBlocker.operatorDomainClosure
  ]

/-- The 003A sub-blocker list is explicit and stable. -/
theorem phase1_blocker003a_subblockers_v1_are_expected :
    phase1Blocker003AGreenIdentitySubBlockersV1 =
      [ Phase1Blocker003AGreenIdentitySubBlocker.concreteDifferentiableFunctionSpace
      , Phase1Blocker003AGreenIdentitySubBlocker.closedBoundaryUniverse
      , Phase1Blocker003AGreenIdentitySubBlocker.integrationRegularity
      , Phase1Blocker003AGreenIdentitySubBlocker.operatorDomainClosure
      ] := by
  rfl

/--
Concrete selected scalar kinetic operator/function-space pair.

The fields still remain abstract enough to avoid pretending that the repo has
a full differentiable-function-space implementation.
-/
structure ScalarKineticOperatorFunctionSpacePair (Point : Type) where
  integral : ContinuumField Point → Real
  kineticOperator : ContinuumField Point → ContinuumField Point
  trace : TwoSidedBoundaryTrace Point
  FieldSmooth : ContinuumField Point → Prop
  InOperatorDomain : ContinuumField Point → Prop

/-- Convert the selected pair into the earlier scalar boundary problem object. -/
def scalarKineticBoundaryProblemOfPair {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) :
    ScalarKineticBoundaryProblem Point where
  operator_kind := ScalarBoundaryOperatorKind.kineticBox
  function_space_kind :=
    ScalarBoundaryFunctionSpaceKind.smoothCompactSupportOrDecay
  integral := pair.integral
  kineticOperator := pair.kineticOperator
  trace := pair.trace
  FieldSmooth := pair.FieldSmooth
  InOperatorDomain := pair.InOperatorDomain

/-- The pair targets the selected kinetic operator and smooth decay class. -/
theorem scalar_kinetic_boundary_problem_of_pair_selected {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) :
    ScalarKineticBoundaryProblemSelected
      (scalarKineticBoundaryProblemOfPair pair) := by
  constructor <;> rfl

/-- The Green identity statement over the selected scalar kinetic pair. -/
def ScalarKineticGreenIdentityStatement {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) : Prop :=
  ∀ x y : ContinuumField Point,
    pair.InOperatorDomain x →
    pair.InOperatorDomain y →
      ContinuumPair pair.integral x (pair.kineticOperator y) =
        ContinuumPair pair.integral y (pair.kineticOperator x) +
          twoSidedBoundaryFlux pair.trace x y

/--
Assumption bundle required to turn the 003A target into a checked boundary
route under the current formal model.
-/
structure ScalarKineticGreenIdentityAssumptionBundle {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) where
  differentiable_function_space_model : Prop
  differentiable_function_space_model_supplied :
    differentiable_function_space_model
  integration_regular : Prop
  integration_regular_supplied : integration_regular
  operator_domain_closure : Prop
  operator_domain_closure_supplied : operator_domain_closure
  green_identity : ScalarKineticGreenIdentityStatement pair
  closed_universe :
    ClosedScalarKineticBoundaryUniverse
      (scalarKineticBoundaryProblemOfPair pair)

/-- A supplied assumption bundle gives the selected Green-identity statement. -/
theorem scalar_kinetic_green_identity_statement_of_bundle {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (bundle : ScalarKineticGreenIdentityAssumptionBundle pair) :
    ScalarKineticGreenIdentityStatement pair :=
  bundle.green_identity

/-- A supplied assumption bundle yields the retained 003A Green-identity object. -/
def retainedGreenIdentityOfAssumptionBundle {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (bundle : ScalarKineticGreenIdentityAssumptionBundle pair) :
    Phase1Blocker003AGreenIdentityRetained
      (scalarKineticBoundaryProblemOfPair pair) where
  blocker_id := rfl
  selected := scalar_kinetic_boundary_problem_of_pair_selected pair
  green_identity := bundle.green_identity

/--
If the concrete 003A assumption bundle is supplied, the scalar kinetic
integration-by-parts identity follows through the existing boundary route.
-/
theorem scalar_kinetic_green_identity_assumption_bundle_suffices_for_ibp
    {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (bundle : ScalarKineticGreenIdentityAssumptionBundle pair)
    (x y : ContinuumField Point) :
    ContinuumPair pair.integral x (pair.kineticOperator y) =
      ContinuumPair pair.integral y (pair.kineticOperator x) := by
  exact scalar_kinetic_retained_green_identity_suffices_for_ibp
    (scalarKineticBoundaryProblemOfPair pair)
    (retainedGreenIdentityOfAssumptionBundle pair bundle)
    bundle.closed_universe
    x y

/--
003A attempt readout.  The Green identity is not unconditionally discharged:
the current model requires the concrete assumption bundle above.
-/
def phase1Blocker003AGreenIdentityAttemptV1 : Phase1Blocker003Split where
  boundaryTermVanishingStatus := .dischargedConditional
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after the 003A discharge attempt. -/
theorem phase1_blocker003a_attempt_v1_phase2_not_authorized :
    ¬ phase1Blocker003AGreenIdentityAttemptV1.phase2Authorized := by
  intro h
  exact h

end
end ContinuumGreenIdentityAttempt
end QFT
end ToeFormal
