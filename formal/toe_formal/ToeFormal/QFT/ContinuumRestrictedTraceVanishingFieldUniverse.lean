/-
ToeFormal/QFT/ContinuumRestrictedTraceVanishingFieldUniverse.lean

Bounded restricted trace-vanishing field-universe attempt for
PHASE1-BLOCKER-003A2A3.

Scope:
- define the restricted field class whose left and right anchored endpoint
  traces vanish
- prove the class excludes the constant-one field, so it is not the full field
  universe
- prove every member of the restricted class supplies the zero-trace condition
- conditionally build the existing full-field `ClosedScalarKineticBoundaryUniverse`
  only from the stronger assumption that every field belongs to the restricted
  class
- prove that stronger full-field assumption is impossible for the meaningful
  anchored trace
- retain the API-level bridge from a restricted class to the existing full-field
  closed-universe route
- keep Phase 2 authorization, nonzero kinetic analysis, operator-domain
  closure, residual separation, and continuum analytic closure out of scope
-/

import ToeFormal.QFT.ContinuumMeaningfulTraceModelAttempt

namespace ToeFormal
namespace QFT
namespace ContinuumRestrictedTraceVanishingFieldUniverse

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumClosedBoundaryUniverseDischargeAttempt
open ContinuumNontrivialClosedBoundaryUniverseAttempt
open ContinuumMeaningfulTraceModelAttempt

set_option autoImplicit false

noncomputable section

/-- Retained blocker after the restricted trace-vanishing field-universe slice. -/
def phase1Blocker003A2A3RestrictedTraceVanishingFieldUniverseRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A3_RESTRICTED_TRACE_VANISHING_FIELD_UNIVERSE_RETAINED"

/-- Outcome id for the bounded restricted trace-vanishing field-class slice. -/
def restrictedTraceVanishingFieldUniverseOutcomeId : String :=
  "RESTRICTED_TRACE_VANISHING_FIELD_CLASS_CONSTRUCTED_" ++
    "FULL_FIELD_CLOSED_UNIVERSE_RETAINED"

/-- Missing objects after the restricted trace-vanishing field-universe attempt. -/
inductive Phase1Blocker003A2A3MissingObject where
  | restrictedClassToClosedUniverseApiBridge
  | closedUniverseOverRestrictedFieldType
  | nonzeroScalarKineticOperator
  | greenIdentityForNonzeroOperator
  | operatorDomainClosureForNonzeroOperator
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A2A3 objects. -/
def phase1Blocker003A2A3MissingObjectId :
    Phase1Blocker003A2A3MissingObject -> String
  | .restrictedClassToClosedUniverseApiBridge =>
      "003A2A3_RESTRICTED_CLASS_TO_CLOSED_UNIVERSE_API_BRIDGE_RETAINED"
  | .closedUniverseOverRestrictedFieldType =>
      "003A2A3_CLOSED_UNIVERSE_OVER_RESTRICTED_FIELD_TYPE_RETAINED"
  | .nonzeroScalarKineticOperator =>
      "003A2A3_NONZERO_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .greenIdentityForNonzeroOperator =>
      "003A2A3_GREEN_IDENTITY_FOR_NONZERO_OPERATOR_RETAINED"
  | .operatorDomainClosureForNonzeroOperator =>
      "003A2A3_OPERATOR_DOMAIN_CLOSURE_FOR_NONZERO_OPERATOR_RETAINED"

/-- The explicit remaining objects after this bounded attempt. -/
def phase1Blocker003A2A3MissingObjectsV0 :
    List Phase1Blocker003A2A3MissingObject :=
  [ .restrictedClassToClosedUniverseApiBridge
  , .closedUniverseOverRestrictedFieldType
  , .nonzeroScalarKineticOperator
  , .greenIdentityForNonzeroOperator
  , .operatorDomainClosureForNonzeroOperator
  ]

/-- The retained-object list is stable and explicit. -/
theorem phase1_blocker003a2a3_missing_objects_v0_expected :
    phase1Blocker003A2A3MissingObjectsV0 =
      [ .restrictedClassToClosedUniverseApiBridge
      , .closedUniverseOverRestrictedFieldType
      , .nonzeroScalarKineticOperator
      , .greenIdentityForNonzeroOperator
      , .operatorDomainClosureForNonzeroOperator
      ] := by
  rfl

/-- Restricted field class: left and right anchored endpoint traces vanish. -/
def AnchoredTraceVanishingFieldClass {Point : Type} [Inhabited Point]
    (f : ContinuumField Point) : Prop :=
  TraceVanishingCompactSupportOrDecay
    (anchoredTraceZeroOperatorBoundaryProblem Point) f

/-- A structured restricted field universe for the meaningful anchored trace. -/
structure RestrictedTraceVanishingFieldUniverse (Point : Type)
    [Inhabited Point] where
  FieldClass : ContinuumField Point -> Prop
  member_left_trace_zero :
    ∀ f : ContinuumField Point,
      FieldClass f ->
        (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).leftTrace f = 0
  member_right_trace_zero :
    ∀ f : ContinuumField Point,
      FieldClass f ->
        (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).rightTrace f = 0
  constant_one_excluded : Not (FieldClass (@constantOneField Point))

/-- Members of the anchored restricted field class have zero left trace. -/
theorem anchored_trace_vanishing_class_left_trace_zero {Point : Type}
    [Inhabited Point] (f : ContinuumField Point)
    (hf : AnchoredTraceVanishingFieldClass f) :
    (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).leftTrace f = 0 := by
  rcases hf with ⟨hLeft, _hRight⟩
  simpa [AnchoredTraceVanishingFieldClass,
    anchoredTraceZeroOperatorBoundaryProblem,
    scalarKineticBoundaryProblemOfPair,
    anchoredTraceZeroOperatorClosedBoundaryPair] using hLeft

/-- Members of the anchored restricted field class have zero right trace. -/
theorem anchored_trace_vanishing_class_right_trace_zero {Point : Type}
    [Inhabited Point] (f : ContinuumField Point)
    (hf : AnchoredTraceVanishingFieldClass f) :
    (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).rightTrace f = 0 := by
  rcases hf with ⟨_hLeft, hRight⟩
  simpa [AnchoredTraceVanishingFieldClass,
    anchoredTraceZeroOperatorBoundaryProblem,
    scalarKineticBoundaryProblemOfPair,
    anchoredTraceZeroOperatorClosedBoundaryPair] using hRight

/-- The anchored restricted class supplies the zero-trace condition. -/
theorem anchored_trace_vanishing_class_has_zero_traces {Point : Type}
    [Inhabited Point] (f : ContinuumField Point)
    (hf : AnchoredTraceVanishingFieldClass f) :
    (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).leftTrace f = 0 ∧
      (@anchoredMeaningfulTwoSidedBoundaryTrace Point _).rightTrace f = 0 := by
  exact ⟨anchored_trace_vanishing_class_left_trace_zero f hf,
    anchored_trace_vanishing_class_right_trace_zero f hf⟩

/-- The restricted class excludes the constant-one field. -/
theorem anchored_trace_vanishing_class_excludes_constant_one
    {Point : Type} [Inhabited Point] :
    Not (AnchoredTraceVanishingFieldClass (@constantOneField Point)) := by
  exact anchored_trace_constant_one_not_trace_vanishing

/-- The restricted class is not the full field universe. -/
theorem anchored_trace_vanishing_class_not_full {Point : Type}
    [Inhabited Point] :
    Not (∀ f : ContinuumField Point, AnchoredTraceVanishingFieldClass f) := by
  intro hAll
  exact anchored_trace_vanishing_class_excludes_constant_one
    (hAll (@constantOneField Point))

/-- Concrete restricted field universe for the anchored meaningful trace. -/
def anchoredRestrictedTraceVanishingFieldUniverse
    (Point : Type) [Inhabited Point] :
    RestrictedTraceVanishingFieldUniverse Point where
  FieldClass := AnchoredTraceVanishingFieldClass
  member_left_trace_zero :=
    anchored_trace_vanishing_class_left_trace_zero
  member_right_trace_zero :=
    anchored_trace_vanishing_class_right_trace_zero
  constant_one_excluded :=
    anchored_trace_vanishing_class_excludes_constant_one

/--
Conditional adapter into the current full-field closed-universe API.

This requires the stronger all-fields trace-vanishing assumption.  The theorem
below proves that assumption is impossible for the meaningful anchored trace,
so this is an adapter statement rather than a discharge.
-/
def closedBoundaryUniverseOfFullFieldTraceVanishingAssumption
    {Point : Type} [Inhabited Point]
    (hAll :
      ∀ f : ContinuumField Point, AnchoredTraceVanishingFieldClass f) :
    ClosedScalarKineticBoundaryUniverse
      (anchoredTraceZeroOperatorBoundaryProblem Point) where
  all_fields_smooth := by
    intro f
    trivial
  all_fields_decay := by
    intro f
    exact hAll f
  all_fields_in_operator_domain := by
    intro f
    trivial

/-- The full-field assumption needed by the adapter is impossible. -/
theorem full_field_trace_vanishing_assumption_impossible
    {Point : Type} [Inhabited Point] :
    Not (∀ f : ContinuumField Point, AnchoredTraceVanishingFieldClass f) := by
  exact anchored_trace_vanishing_class_not_full

/-- The restricted class alone does not feed the current full-field API. -/
theorem restricted_class_alone_does_not_feed_current_closed_universe
    {Point : Type} [Inhabited Point] :
    Not (AnchoredMeaningfulTraceFeedsClosedBoundaryUniverse Point) := by
  exact anchored_meaningful_trace_cannot_feed_closed_boundary_universe

/-- Status readout for this bounded restricted field-universe attempt. -/
structure RestrictedTraceVanishingFieldUniverseAttemptStatus where
  restricted_field_class_constructed : Prop
  constant_one_excluded : Prop
  members_have_zero_trace : Prop
  conditional_full_field_adapter_recorded : Prop
  full_field_assumption_refuted : Prop
  full_field_assumption_refutation_supplied : full_field_assumption_refuted
  current_closed_universe_constructed : Prop
  current_closed_universe_not_constructed :
    Not current_closed_universe_constructed
  nonzero_operator_green_identity_closed : Prop
  nonzero_operator_green_identity_not_closed :
    Not nonzero_operator_green_identity_closed
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized
  parent_retained_blocker_id : String
  retained_blocker_id : String
  outcome_id : String

/-- Versioned status object for this attempt. -/
def restrictedTraceVanishingFieldUniverseAttemptStatusV0 :
    RestrictedTraceVanishingFieldUniverseAttemptStatus where
  restricted_field_class_constructed := True
  constant_one_excluded := True
  members_have_zero_trace := True
  conditional_full_field_adapter_recorded := True
  full_field_assumption_refuted :=
    ∀ (Point : Type) [Inhabited Point],
      Not (∀ f : ContinuumField Point,
        AnchoredTraceVanishingFieldClass f)
  full_field_assumption_refutation_supplied := by
    intro Point inst
    exact full_field_trace_vanishing_assumption_impossible
  current_closed_universe_constructed :=
    ∀ (Point : Type) [Inhabited Point],
      AnchoredMeaningfulTraceFeedsClosedBoundaryUniverse Point
  current_closed_universe_not_constructed := by
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
    phase1Blocker003A2A2MeaningfulTraceModelRetainedId
  retained_blocker_id :=
    phase1Blocker003A2A3RestrictedTraceVanishingFieldUniverseRetainedId
  outcome_id := restrictedTraceVanishingFieldUniverseOutcomeId

/-- Short local status alias. -/
def restrictedTraceVanishingAttemptStatusV0 :
    RestrictedTraceVanishingFieldUniverseAttemptStatus :=
  restrictedTraceVanishingFieldUniverseAttemptStatusV0

/-- The restricted field class is constructed. -/
theorem restricted_trace_vanishing_class_constructed_v0 :
    restrictedTraceVanishingAttemptStatusV0.restricted_field_class_constructed := by
  trivial

/-- The restricted field class excludes the constant-one field. -/
theorem restricted_trace_vanishing_constant_one_excluded_v0 :
    restrictedTraceVanishingAttemptStatusV0.constant_one_excluded := by
  trivial

/-- Members of the restricted class have zero traces. -/
theorem restricted_trace_vanishing_members_have_zero_trace_v0 :
    restrictedTraceVanishingAttemptStatusV0.members_have_zero_trace := by
  trivial

/-- The conditional adapter into the full-field API is recorded. -/
theorem restricted_trace_vanishing_conditional_adapter_recorded_v0 :
    restrictedTraceVanishingAttemptStatusV0.conditional_full_field_adapter_recorded := by
  trivial

/-- The all-field trace-vanishing assumption is refuted. -/
theorem restricted_trace_vanishing_full_field_assumption_refuted_v0 :
    restrictedTraceVanishingAttemptStatusV0.full_field_assumption_refuted := by
  exact restrictedTraceVanishingAttemptStatusV0
    |>.full_field_assumption_refutation_supplied

/-- The current full-field closed universe remains unconstructed. -/
theorem restricted_trace_vanishing_current_closed_universe_not_constructed_v0 :
    Not restrictedTraceVanishingAttemptStatusV0.current_closed_universe_constructed := by
  exact restrictedTraceVanishingAttemptStatusV0
    |>.current_closed_universe_not_constructed

/-- The nonzero-operator Green identity remains retained. -/
theorem restricted_trace_vanishing_nonzero_operator_green_not_closed_v0 :
    Not restrictedTraceVanishingAttemptStatusV0.nonzero_operator_green_identity_closed := by
  exact restrictedTraceVanishingAttemptStatusV0
    |>.nonzero_operator_green_identity_not_closed

/-- The attempt exposes the parent retained blocker id. -/
theorem restricted_trace_vanishing_parent_retained_id_v0 :
    restrictedTraceVanishingAttemptStatusV0.parent_retained_blocker_id =
      phase1Blocker003A2A2MeaningfulTraceModelRetainedId := by
  rfl

/-- The attempt exposes the retained blocker id. -/
theorem restricted_trace_vanishing_retained_id_v0 :
    restrictedTraceVanishingAttemptStatusV0.retained_blocker_id =
      phase1Blocker003A2A3RestrictedTraceVanishingFieldUniverseRetainedId := by
  rfl

/-- The attempt exposes the outcome id. -/
theorem restricted_trace_vanishing_outcome_id_v0 :
    restrictedTraceVanishingAttemptStatusV0.outcome_id =
      restrictedTraceVanishingFieldUniverseOutcomeId := by
  rfl

/-- Phase 2 remains unauthorized after this bounded attempt. -/
theorem restricted_trace_vanishing_attempt_phase2_not_authorized_v0 :
    Not restrictedTraceVanishingAttemptStatusV0.phase2Authorized := by
  exact restrictedTraceVanishingAttemptStatusV0.phase2_not_authorized

/--
Readout for the parent Blocker 003 split.  The restricted class exists, but the
current full-field closed-universe API is still not satisfied.
-/
def phase1Blocker003A2A3RestrictedTraceVanishingAttemptV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized in the parent readout. -/
theorem phase1_blocker003a2a3_restricted_trace_v0_phase2_not_authorized :
    Not phase1Blocker003A2A3RestrictedTraceVanishingAttemptV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumRestrictedTraceVanishingFieldUniverse
end QFT
end ToeFormal
