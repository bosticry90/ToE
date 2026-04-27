/-
ToeFormal/QFT/ContinuumConcreteCalculusSemantics.lean

Bounded concrete-calculus semantics adapter for PHASE1-BLOCKER-003A1.

Scope:
- define the semantics object that would instantiate the 003A1
  differentiable-function-space witness
- construct the 003A1 witness from that supplied semantics object
- prove that the supplied semantics gives the differentiability model and
  trace/variation consequences already needed by the Green-identity route
- record the exact remaining calculus objects when no concrete semantics source
  is supplied by the current repo
- keep Green identity, closed boundary universe, integration regularity,
  operator-domain closure, residual separation, and Phase 2 authorization out
  of scope
-/

import ToeFormal.QFT.ContinuumDifferentiableFunctionSpace

namespace ToeFormal
namespace QFT
namespace ContinuumConcreteCalculusSemantics

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
open ContinuumDifferentiableFunctionSpace
set_option autoImplicit false

noncomputable section

/-- Exact retained id for the missing concrete-calculus semantics layer. -/
def phase1Blocker003A1ConcreteCalculusSemanticsId : String :=
  "PHASE1-BLOCKER-003A1A_CONCRETE_CALCULUS_SEMANTICS_RETAINED"

/-- Concrete objects still needed to turn the 003A1 witness into a real model. -/
inductive Phase1Blocker003A1ConcreteCalculusMissingObject where
  | baseSpaceAndIntegralModel
  | differentiabilityRegularityInterpretation
  | compactSupportDecayInterpretation
  | traceExistenceAndVanishingTheorem
  | variationClosureTheorem
  | scalarKineticPairCompatibility
deriving DecidableEq, Repr

/-- Machine-facing ids for the remaining 003A1 concrete-calculus objects. -/
def phase1Blocker003A1ConcreteCalculusMissingObjectId :
    Phase1Blocker003A1ConcreteCalculusMissingObject → String
  | .baseSpaceAndIntegralModel =>
      "003A1A_BASE_SPACE_AND_INTEGRAL_MODEL_RETAINED"
  | .differentiabilityRegularityInterpretation =>
      "003A1A_DIFFERENTIABILITY_REGULARITY_INTERPRETATION_RETAINED"
  | .compactSupportDecayInterpretation =>
      "003A1A_COMPACT_SUPPORT_DECAY_INTERPRETATION_RETAINED"
  | .traceExistenceAndVanishingTheorem =>
      "003A1A_TRACE_EXISTENCE_AND_VANISHING_THEOREM_RETAINED"
  | .variationClosureTheorem =>
      "003A1A_VARIATION_CLOSURE_THEOREM_RETAINED"
  | .scalarKineticPairCompatibility =>
      "003A1A_SCALAR_KINETIC_PAIR_COMPATIBILITY_RETAINED"

/-- Exact retained calculus objects after the semantics-instantiation attempt. -/
def phase1Blocker003A1ConcreteCalculusMissingObjectsV0 :
    List Phase1Blocker003A1ConcreteCalculusMissingObject :=
  [ .baseSpaceAndIntegralModel
  , .differentiabilityRegularityInterpretation
  , .compactSupportDecayInterpretation
  , .traceExistenceAndVanishingTheorem
  , .variationClosureTheorem
  , .scalarKineticPairCompatibility
  ]

/-- The current concrete-calculus retained-object list is explicit. -/
theorem phase1_blocker003a1_concrete_calculus_missing_objects_v0_expected :
    phase1Blocker003A1ConcreteCalculusMissingObjectsV0 =
      [ .baseSpaceAndIntegralModel
      , .differentiabilityRegularityInterpretation
      , .compactSupportDecayInterpretation
      , .traceExistenceAndVanishingTheorem
      , .variationClosureTheorem
      , .scalarKineticPairCompatibility
      ] := by
  rfl

/--
Concrete calculus semantics sufficient to instantiate the 003A1 witness.

This is still an input object, not a constructed real-analysis model.  Its
fields state exactly what a concrete calculus implementation must provide.
-/
structure ConcreteCalculusSemantics {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) where
  FieldSpace : ContinuumField Point → Prop
  TestVariationSpace : ContinuumField Point → Prop
  DifferentiableRegular : ContinuumField Point → Prop
  CompactSupportOrBoundaryDecay : ContinuumField Point → Prop
  TraceExists : ContinuumField Point → Prop
  calculus_semantics_source : Prop
  calculus_semantics_source_supplied : calculus_semantics_source
  field_regular :
    ∀ f : ContinuumField Point,
      FieldSpace f → DifferentiableRegular f
  variation_regular :
    ∀ eta : ContinuumField Point,
      TestVariationSpace eta → DifferentiableRegular eta
  field_smooth :
    ∀ f : ContinuumField Point,
      FieldSpace f → pair.FieldSmooth f
  variation_smooth :
    ∀ eta : ContinuumField Point,
      TestVariationSpace eta → pair.FieldSmooth eta
  field_decay :
    ∀ f : ContinuumField Point,
      FieldSpace f → CompactSupportOrBoundaryDecay f
  variation_decay :
    ∀ eta : ContinuumField Point,
      TestVariationSpace eta → CompactSupportOrBoundaryDecay eta
  field_trace_exists :
    ∀ f : ContinuumField Point,
      FieldSpace f → TraceExists f
  variation_trace_exists :
    ∀ eta : ContinuumField Point,
      TestVariationSpace eta → TraceExists eta
  trace_vanishing_of_decay :
    ∀ f : ContinuumField Point,
      CompactSupportOrBoundaryDecay f →
        TraceVanishingCompactSupportOrDecay
          (scalarKineticBoundaryProblemOfPair pair) f
  variation_family_closed :
    ∀ (phi eta : ContinuumField Point) (eps : Real),
      FieldSpace phi →
      TestVariationSpace eta →
        FieldSpace (VariationFamily phi eta eps)
  test_variations_add_closed :
    ∀ eta zeta : ContinuumField Point,
      TestVariationSpace eta →
      TestVariationSpace zeta →
        TestVariationSpace (fieldAdd eta zeta)
  test_variations_smul_closed :
    ∀ (a : Real) (eta : ContinuumField Point),
      TestVariationSpace eta →
        TestVariationSpace (fieldSMul a eta)

/-- A supplied concrete-calculus semantics object builds the 003A1 witness. -/
def witnessOfConcreteCalculusSemantics {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair) :
    ScalarKineticDifferentiableFunctionSpaceWitness pair where
  FieldSpace := semantics.FieldSpace
  TestVariationSpace := semantics.TestVariationSpace
  DifferentiableRegular := semantics.DifferentiableRegular
  CompactSupportOrBoundaryDecay := semantics.CompactSupportOrBoundaryDecay
  TraceExists := semantics.TraceExists
  field_regular := semantics.field_regular
  variation_regular := semantics.variation_regular
  field_smooth := semantics.field_smooth
  variation_smooth := semantics.variation_smooth
  field_decay := semantics.field_decay
  variation_decay := semantics.variation_decay
  field_trace_exists := semantics.field_trace_exists
  variation_trace_exists := semantics.variation_trace_exists
  trace_vanishing_of_decay := semantics.trace_vanishing_of_decay
  variation_family_closed := semantics.variation_family_closed
  test_variations_add_closed := semantics.test_variations_add_closed
  test_variations_smul_closed := semantics.test_variations_smul_closed

/-- Concrete-calculus semantics supplies the 003A1 differentiability model. -/
theorem concrete_calculus_semantics_supplies_function_space_model
    {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair) :
    ScalarKineticDifferentiableFunctionSpaceModel pair := by
  exact function_space_witness_supplies_differentiability_portion
    pair (witnessOfConcreteCalculusSemantics pair semantics)

/-- The semantics source field is an explicit retained input, not implicit prose. -/
theorem concrete_calculus_semantics_source_is_supplied {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair) :
    semantics.calculus_semantics_source :=
  semantics.calculus_semantics_source_supplied

/-- Concrete-calculus semantics gives regularity for selected fields. -/
theorem concrete_calculus_field_space_member_regular {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair)
    (f : ContinuumField Point)
    (hf : semantics.FieldSpace f) :
    semantics.DifferentiableRegular f :=
  semantics.field_regular f hf

/-- Concrete-calculus semantics gives regularity for selected variations. -/
theorem concrete_calculus_test_variation_regular {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair)
    (eta : ContinuumField Point)
    (heta : semantics.TestVariationSpace eta) :
    semantics.DifferentiableRegular eta :=
  semantics.variation_regular eta heta

/-- Concrete-calculus semantics keeps allowed variation families in field space. -/
theorem concrete_calculus_variation_family_closed {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair)
    (phi eta : ContinuumField Point)
    (eps : Real)
    (hphi : semantics.FieldSpace phi)
    (heta : semantics.TestVariationSpace eta) :
    semantics.FieldSpace (VariationFamily phi eta eps) :=
  semantics.variation_family_closed phi eta eps hphi heta

/-- Concrete-calculus decay data gives trace vanishing for the selected pair. -/
theorem concrete_calculus_decay_gives_trace_vanishing {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (semantics : ConcreteCalculusSemantics pair)
    (f : ContinuumField Point)
    (hf : semantics.CompactSupportOrBoundaryDecay f) :
    TraceVanishingCompactSupportOrDecay
      (scalarKineticBoundaryProblemOfPair pair) f :=
  semantics.trace_vanishing_of_decay f hf

/--
003A1A readout.  The adapter from concrete calculus semantics to the 003A1
witness is landed, but an actual concrete calculus source is still retained.
-/
def phase1Blocker003A1ConcreteCalculusSemanticsV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .dischargedConditional
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after the concrete-calculus adapter increment. -/
theorem phase1_blocker003a1_concrete_calculus_v0_phase2_not_authorized :
    ¬ phase1Blocker003A1ConcreteCalculusSemanticsV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumConcreteCalculusSemantics
end QFT
end ToeFormal
