/-
ToeFormal/QFT/ContinuumRestrictedClosedBoundaryUniverseAPI.lean

Restricted closed-boundary-universe API surface for
PHASE1-BLOCKER-003A2A4.

Scope:
- define a restricted closed scalar kinetic boundary universe over a field
  class instead of over all continuum fields
- define a restricted boundary-term model and restricted integration-by-parts
  route over that class
- instantiate the restricted API for the meaningful anchored trace and its
  trace-vanishing field class
- prove restricted integration by parts for the zero-operator witness
- record that this restricted API still does not feed the existing full-field
  `BoundaryTermModel` or Phase 2 route without a separate bridge
- keep nonzero kinetic analysis, full-field API bridge, operator-domain closure,
  residual separation, and continuum analytic closure out of scope
-/

import ToeFormal.QFT.ContinuumRestrictedTraceVanishingFieldUniverse

namespace ToeFormal
namespace QFT
namespace ContinuumRestrictedClosedBoundaryUniverseAPI

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumMeaningfulTraceModelAttempt
open ContinuumRestrictedTraceVanishingFieldUniverse

set_option autoImplicit false

noncomputable section

/-- Retained blocker after defining the restricted closed-boundary API. -/
def phase1Blocker003A2A4RestrictedClosedBoundaryUniverseApiRequiredId :
    String :=
  "PHASE1-BLOCKER-003A2A4_RESTRICTED_CLOSED_BOUNDARY_UNIVERSE_API_REQUIRED"

/-- Outcome id for the restricted API slice. -/
def restrictedClosedBoundaryUniverseApiOutcomeId : String :=
  "RESTRICTED_CLOSED_BOUNDARY_UNIVERSE_API_DEFINED_" ++
    "FULL_FIELD_BRIDGE_RETAINED"

/-- Missing objects after the restricted API slice. -/
inductive Phase1Blocker003A2A4MissingObject where
  | restrictedToFullBoundaryTermModelBridge
  | restrictedFirstVariationRoute
  | nonzeroScalarKineticOperator
  | greenIdentityForNonzeroOperator
  | operatorDomainClosureForNonzeroOperator
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A4 objects. -/
def phase1Blocker003A2A4MissingObjectId :
    Phase1Blocker003A2A4MissingObject -> String
  | .restrictedToFullBoundaryTermModelBridge =>
      "003A2A4_RESTRICTED_TO_FULL_BOUNDARY_TERM_MODEL_BRIDGE_RETAINED"
  | .restrictedFirstVariationRoute =>
      "003A2A4_RESTRICTED_FIRST_VARIATION_ROUTE_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A4_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .greenIdentityForNonzeroOperator =>
      "003A2A4_GREEN_IDENTITY_FOR_NONZERO_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A4_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"

/-- The explicit remaining objects after this bounded attempt. -/
def phase1Blocker003A2A4MissingObjectsV0 :
    List Phase1Blocker003A2A4MissingObject :=
  [ .restrictedToFullBoundaryTermModelBridge
  , .restrictedFirstVariationRoute
  , .nonzeroScalarKineticOperator
  , .greenIdentityForNonzeroOperator
  , .operatorDomainClosureForNonzeroOperator
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a4_missing_objects_v0_expected :
    phase1Blocker003A2A4MissingObjectsV0 =
      [ .restrictedToFullBoundaryTermModelBridge
      , .restrictedFirstVariationRoute
      , .nonzeroScalarKineticOperator
      , .greenIdentityForNonzeroOperator
      , .operatorDomainClosureForNonzeroOperator
      ] := by
  rfl

/-- Closed scalar kinetic boundary universe over a restricted field class. -/
structure RestrictedClosedScalarKineticBoundaryUniverse {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point) where
  FieldClass : ContinuumField Point -> Prop
  all_restricted_fields_smooth :
    ∀ f : ContinuumField Point, FieldClass f -> problem.FieldSmooth f
  all_restricted_fields_decay :
    ∀ f : ContinuumField Point,
      FieldClass f -> TraceVanishingCompactSupportOrDecay problem f
  all_restricted_fields_in_operator_domain :
    ∀ f : ContinuumField Point, FieldClass f -> problem.InOperatorDomain f

/-- Green identity over a restricted field class. -/
def RestrictedScalarKineticGreenIdentityStatement {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (FieldClass : ContinuumField Point -> Prop) : Prop :=
  ∀ x y : ContinuumField Point,
    FieldClass x ->
    FieldClass y ->
      ContinuumPair problem.integral x (problem.kineticOperator y) =
        ContinuumPair problem.integral y (problem.kineticOperator x) +
          twoSidedBoundaryFlux problem.trace x y

/-- Boundary-term model over a restricted field class. -/
structure RestrictedBoundaryTermModel {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point) where
  FieldClass : ContinuumField Point -> Prop
  boundaryTerm : ContinuumField Point -> ContinuumField Point -> Real
  integration_by_parts_with_boundary :
    ∀ x y : ContinuumField Point,
      FieldClass x ->
      FieldClass y ->
        ContinuumPair integral x (operator y) =
          ContinuumPair integral y (operator x) + boundaryTerm x y
  boundary_vanishes :
    ∀ x y : ContinuumField Point,
      FieldClass x -> FieldClass y -> boundaryTerm x y = 0

/-- Restricted boundary model from a restricted closed universe and Green identity. -/
def restrictedBoundaryTermModelOfRestrictedClosedUniverse {Point : Type}
    (problem : ScalarKineticBoundaryProblem Point)
    (closed : RestrictedClosedScalarKineticBoundaryUniverse problem)
    (green :
      RestrictedScalarKineticGreenIdentityStatement problem closed.FieldClass) :
    RestrictedBoundaryTermModel problem.integral problem.kineticOperator where
  FieldClass := closed.FieldClass
  boundaryTerm := twoSidedBoundaryFlux problem.trace
  integration_by_parts_with_boundary := green
  boundary_vanishes := by
    intro x y hx hy
    rcases closed.all_restricted_fields_decay x hx with ⟨hxLeft, hxRight⟩
    rcases closed.all_restricted_fields_decay y hy with ⟨hyLeft, hyRight⟩
    simp [twoSidedBoundaryFlux, hxLeft, hxRight, hyLeft, hyRight]

/-- Restricted boundary vanishing gives restricted integration by parts. -/
theorem restricted_boundary_term_model_suffices_for_restricted_ibp
    {Point : Type}
    (integral : ContinuumField Point -> Real)
    (operator : ContinuumField Point -> ContinuumField Point)
    (model : RestrictedBoundaryTermModel integral operator)
    (x y : ContinuumField Point)
    (hx : model.FieldClass x)
    (hy : model.FieldClass y) :
    ContinuumPair integral x (operator y) =
      ContinuumPair integral y (operator x) := by
  rw [model.integration_by_parts_with_boundary x y hx hy]
  rw [model.boundary_vanishes x y hx hy]
  ring

/-- Generic adapter into the old full-field API, requiring all fields in class. -/
def fullClosedUniverseOfRestrictedClosedUniverseAndAllFields
    {Point : Type}
    {problem : ScalarKineticBoundaryProblem Point}
    (closed : RestrictedClosedScalarKineticBoundaryUniverse problem)
    (hAll : ∀ f : ContinuumField Point, closed.FieldClass f) :
    ClosedScalarKineticBoundaryUniverse problem where
  all_fields_smooth := by
    intro f
    exact closed.all_restricted_fields_smooth f (hAll f)
  all_fields_decay := by
    intro f
    exact closed.all_restricted_fields_decay f (hAll f)
  all_fields_in_operator_domain := by
    intro f
    exact closed.all_restricted_fields_in_operator_domain f (hAll f)

/-- Zero field is in the anchored trace-vanishing restricted class. -/
theorem zero_field_in_anchored_trace_vanishing_class {Point : Type}
    [Inhabited Point] :
    AnchoredTraceVanishingFieldClass (@zeroField Point) := by
  simp [AnchoredTraceVanishingFieldClass,
    TraceVanishingCompactSupportOrDecay,
    anchoredTraceZeroOperatorBoundaryProblem,
    scalarKineticBoundaryProblemOfPair,
    anchoredTraceZeroOperatorClosedBoundaryPair,
    anchoredMeaningfulTwoSidedBoundaryTrace,
    zeroField]

/-- Restricted closed universe for the anchored meaningful trace. -/
def anchoredRestrictedClosedScalarKineticBoundaryUniverse
    (Point : Type) [Inhabited Point] :
    RestrictedClosedScalarKineticBoundaryUniverse
      (anchoredTraceZeroOperatorBoundaryProblem Point) where
  FieldClass := AnchoredTraceVanishingFieldClass
  all_restricted_fields_smooth := by
    intro f hf
    trivial
  all_restricted_fields_decay := by
    intro f hf
    exact hf
  all_restricted_fields_in_operator_domain := by
    intro f hf
    trivial

/-- The anchored restricted API has a nonempty field class. -/
theorem anchored_restricted_field_class_nonempty {Point : Type}
    [Inhabited Point] :
    ∃ f : ContinuumField Point,
      (anchoredRestrictedClosedScalarKineticBoundaryUniverse Point).FieldClass f := by
  exact ⟨@zeroField Point, zero_field_in_anchored_trace_vanishing_class⟩

/-- The anchored restricted API excludes the constant-one field. -/
theorem anchored_restricted_closed_universe_excludes_constant_one
    {Point : Type} [Inhabited Point] :
    Not ((anchoredRestrictedClosedScalarKineticBoundaryUniverse Point).FieldClass
      (@constantOneField Point)) := by
  exact anchored_trace_vanishing_class_excludes_constant_one

/-- Restricted zero-operator Green identity for the anchored meaningful trace. -/
theorem anchored_restricted_zero_operator_green_identity_statement
    {Point : Type} [Inhabited Point] :
    RestrictedScalarKineticGreenIdentityStatement
      (anchoredTraceZeroOperatorBoundaryProblem Point)
      (anchoredRestrictedClosedScalarKineticBoundaryUniverse Point).FieldClass := by
  intro x y hx hy
  simp [anchoredTraceZeroOperatorBoundaryProblem,
    scalarKineticBoundaryProblemOfPair,
    anchoredTraceZeroOperatorClosedBoundaryPair,
    anchoredContinuumIntegral,
    zeroKineticOperator,
    anchoredMeaningfulTwoSidedBoundaryTrace,
    ContinuumPair,
    twoSidedBoundaryFlux]

/-- Restricted boundary-term model for the anchored meaningful trace. -/
def anchoredRestrictedBoundaryTermModel (Point : Type) [Inhabited Point] :
    RestrictedBoundaryTermModel
      (@anchoredContinuumIntegral Point _)
      (@zeroKineticOperator Point) :=
  restrictedBoundaryTermModelOfRestrictedClosedUniverse
    (anchoredTraceZeroOperatorBoundaryProblem Point)
    (anchoredRestrictedClosedScalarKineticBoundaryUniverse Point)
    anchored_restricted_zero_operator_green_identity_statement

/-- Restricted integration by parts for fields in the anchored restricted class. -/
theorem anchored_restricted_boundary_model_suffices_for_restricted_ibp
    {Point : Type} [Inhabited Point]
    (x y : ContinuumField Point)
    (hx :
      (anchoredRestrictedBoundaryTermModel Point).FieldClass x)
    (hy :
      (anchoredRestrictedBoundaryTermModel Point).FieldClass y) :
    ContinuumPair (@anchoredContinuumIntegral Point _)
        x ((@zeroKineticOperator Point) y) =
      ContinuumPair (@anchoredContinuumIntegral Point _)
        y ((@zeroKineticOperator Point) x) := by
  exact restricted_boundary_term_model_suffices_for_restricted_ibp
    (@anchoredContinuumIntegral Point _)
    (@zeroKineticOperator Point)
    (anchoredRestrictedBoundaryTermModel Point)
    x y hx hy

/-- The restricted class still cannot become the old full-field universe. -/
theorem anchored_restricted_closed_universe_all_fields_impossible
    {Point : Type} [Inhabited Point] :
    Not (∀ f : ContinuumField Point,
      (anchoredRestrictedClosedScalarKineticBoundaryUniverse Point).FieldClass f) := by
  exact anchored_trace_vanishing_class_not_full

/-- The restricted API alone does not produce the old full-field boundary model. -/
theorem restricted_api_does_not_produce_current_full_field_universe
    {Point : Type} [Inhabited Point] :
    Not (AnchoredMeaningfulTraceFeedsClosedBoundaryUniverse Point) := by
  exact anchored_meaningful_trace_cannot_feed_closed_boundary_universe

/-- Status readout for this bounded restricted API attempt. -/
structure RestrictedClosedBoundaryUniverseApiAttemptStatus where
  restricted_api_defined : Prop
  restricted_universe_constructed : Prop
  restricted_field_class_nonempty : Prop
  constant_one_excluded : Prop
  restricted_zero_operator_ibp_discharged : Prop
  old_full_field_boundary_model_constructed : Prop
  old_full_field_boundary_model_not_constructed :
    Not old_full_field_boundary_model_constructed
  nonzero_operator_green_identity_closed : Prop
  nonzero_operator_green_identity_not_closed :
    Not nonzero_operator_green_identity_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this attempt. -/
def restrictedClosedBoundaryUniverseApiAttemptStatusV0 :
    RestrictedClosedBoundaryUniverseApiAttemptStatus where
  restricted_api_defined := True
  restricted_universe_constructed := True
  restricted_field_class_nonempty := True
  constant_one_excluded := True
  restricted_zero_operator_ibp_discharged := True
  old_full_field_boundary_model_constructed :=
    ∀ (Point : Type) [Inhabited Point],
      AnchoredMeaningfulTraceFeedsClosedBoundaryUniverse Point
  old_full_field_boundary_model_not_constructed := by
    intro h
    exact anchored_meaningful_trace_cannot_feed_closed_boundary_universe
      (h Unit)
  nonzero_operator_green_identity_closed := False
  nonzero_operator_green_identity_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h
  parent_retained_blocker_id :=
    phase1Blocker003A2A3RestrictedTraceVanishingFieldUniverseRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A4RestrictedClosedBoundaryUniverseApiRequiredId
  outcome_id := restrictedClosedBoundaryUniverseApiOutcomeId

/-- Short local status alias. -/
def restrictedClosedBoundaryApiAttemptStatusV0 :
    RestrictedClosedBoundaryUniverseApiAttemptStatus :=
  restrictedClosedBoundaryUniverseApiAttemptStatusV0

/-- The restricted API is defined. -/
theorem restricted_closed_boundary_api_defined_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.restricted_api_defined := by
  trivial

/-- The anchored restricted closed universe is constructed. -/
theorem restricted_closed_boundary_universe_constructed_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.restricted_universe_constructed := by
  trivial

/-- The anchored restricted field class is nonempty. -/
theorem restricted_closed_boundary_field_class_nonempty_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.restricted_field_class_nonempty := by
  trivial

/-- The anchored restricted field class excludes the constant-one field. -/
theorem restricted_closed_boundary_constant_one_excluded_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.constant_one_excluded := by
  trivial

/-- Restricted zero-operator integration by parts is discharged. -/
theorem restricted_closed_boundary_zero_operator_ibp_discharged_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.restricted_zero_operator_ibp_discharged := by
  trivial

/-- The old full-field boundary route remains unconstructed. -/
theorem restricted_closed_boundary_old_full_field_not_constructed_v0 :
    Not restrictedClosedBoundaryApiAttemptStatusV0.old_full_field_boundary_model_constructed := by
  exact restrictedClosedBoundaryApiAttemptStatusV0.old_full_field_boundary_model_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem restricted_closed_boundary_nonzero_operator_green_not_closed_v0 :
    Not restrictedClosedBoundaryApiAttemptStatusV0.nonzero_operator_green_identity_closed := by
  exact restrictedClosedBoundaryApiAttemptStatusV0.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem restricted_closed_boundary_parent_retained_id_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A3RestrictedTraceVanishingFieldUniverseRetainedId := by
  rfl

/-- The attempt exposes the retained blocker id. -/
theorem restricted_closed_boundary_retained_id_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.retained_blocker_id =
      phase1Blocker003A2A4RestrictedClosedBoundaryUniverseApiRequiredId := by
  rfl

/-- The attempt exposes the outcome id. -/
theorem restricted_closed_boundary_outcome_id_v0 :
    restrictedClosedBoundaryApiAttemptStatusV0.outcome_id =
      restrictedClosedBoundaryUniverseApiOutcomeId := by
  rfl

/-- Phase 2 remains unauthorized after this bounded attempt. -/
theorem restricted_closed_boundary_api_phase2_not_authorized_v0 :
    Not restrictedClosedBoundaryApiAttemptStatusV0.phase2Authorized := by
  exact restrictedClosedBoundaryApiAttemptStatusV0.phase2_not_authorized

/--
Readout for the parent Blocker 003 split.  The restricted API exists, but it
does not yet feed the full-field first-variation route.
-/
def phase1Blocker003A2A4RestrictedApiAttemptV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a4_restricted_api_v0_phase2_not_authorized :
    Not phase1Blocker003A2A4RestrictedApiAttemptV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumRestrictedClosedBoundaryUniverseAPI
end QFT
end ToeFormal
