/-
ToeFormal/QFT/ContinuumDifferentiableFunctionSpace.lean

Bounded witness surface for PHASE1-BLOCKER-003A1.

Scope:
- define the smallest differentiable-function-space witness needed by the
  selected scalar kinetic Green-identity route
- expose field space, test-variation space, regularity, compact-support/decay,
  trace-existence, and variation-closure obligations
- prove that such a witness supplies the differentiability portion of the
  `ScalarKineticGreenIdentityAssumptionBundle`
- keep concrete calculus semantics, closed boundary universe, integration
  regularity, operator-domain closure, residual separation, and Phase 2
  authorization out of scope
-/

import ToeFormal.QFT.ContinuumGreenIdentityAttempt

namespace ToeFormal
namespace QFT
namespace ContinuumDifferentiableFunctionSpace

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumBoundaryTermModel
open ContinuumGreenIdentityRetained
open ContinuumGreenIdentityAttempt
set_option autoImplicit false

noncomputable section

/-- Exact retained sub-blocker id for the differentiable-function-space lane. -/
def phase1Blocker003A1DifferentiableFunctionSpaceId : String :=
  "PHASE1-BLOCKER-003A1_DIFFERENTIABLE_FUNCTION_SPACE_RETAINED"

/--
Minimal differentiable-function-space witness for the selected scalar kinetic
Green-identity route.

The predicates are intentionally abstract: this surface records what a
concrete calculus model must provide without pretending that such a model is
already available in the repo.
-/
structure ScalarKineticDifferentiableFunctionSpaceWitness {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) where
  FieldSpace : ContinuumField Point → Prop
  TestVariationSpace : ContinuumField Point → Prop
  DifferentiableRegular : ContinuumField Point → Prop
  CompactSupportOrBoundaryDecay : ContinuumField Point → Prop
  TraceExists : ContinuumField Point → Prop
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
        ContinuumGreenIdentityRetained.TraceVanishingCompactSupportOrDecay
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

/-- Function-space model proposition used by the Green-identity bundle. -/
def ScalarKineticDifferentiableFunctionSpaceModel {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) : Prop :=
  ∃ _witness :
    ScalarKineticDifferentiableFunctionSpaceWitness pair, True

/-- A witness supplies the differentiable-function-space model proposition. -/
theorem differentiable_function_space_model_of_witness {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair) :
    ScalarKineticDifferentiableFunctionSpaceModel pair := by
  exact ⟨witness, True.intro⟩

/-- The differentiability portion of the Green-identity assumption bundle. -/
structure ScalarKineticGreenIdentityDifferentiabilityPortion {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point) where
  differentiable_function_space_model : Prop
  differentiable_function_space_model_supplied :
    differentiable_function_space_model

/--
Package the differentiability portion of the Green-identity bundle from a
function-space witness.
-/
def differentiabilityPortionOfFunctionSpaceWitness {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair) :
    ScalarKineticGreenIdentityDifferentiabilityPortion pair where
  differentiable_function_space_model :=
    ScalarKineticDifferentiableFunctionSpaceModel pair
  differentiable_function_space_model_supplied :=
    differentiable_function_space_model_of_witness pair witness

/-- The packaged differentiability portion is exactly supplied by the witness. -/
theorem function_space_witness_supplies_differentiability_portion
    {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair) :
    ScalarKineticDifferentiableFunctionSpaceModel pair := by
  exact differentiable_function_space_model_of_witness pair witness

/-- Field-space members are regular. -/
theorem field_space_member_regular {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair)
    (f : ContinuumField Point)
    (hf : witness.FieldSpace f) :
    witness.DifferentiableRegular f :=
  witness.field_regular f hf

/-- Test variations are regular. -/
theorem test_variation_regular {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair)
    (eta : ContinuumField Point)
    (heta : witness.TestVariationSpace eta) :
    witness.DifferentiableRegular eta :=
  witness.variation_regular eta heta

/-- Allowed variations stay inside the selected field space. -/
theorem variation_family_stays_in_field_space {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair)
    (phi eta : ContinuumField Point)
    (eps : Real)
    (hphi : witness.FieldSpace phi)
    (heta : witness.TestVariationSpace eta) :
    witness.FieldSpace (VariationFamily phi eta eps) :=
  witness.variation_family_closed phi eta eps hphi heta

/-- Decay in the witness implies trace vanishing for the selected boundary problem. -/
theorem witness_decay_gives_trace_vanishing {Point : Type}
    (pair : ScalarKineticOperatorFunctionSpacePair Point)
    (witness : ScalarKineticDifferentiableFunctionSpaceWitness pair)
    (f : ContinuumField Point)
    (hf : witness.CompactSupportOrBoundaryDecay f) :
    ContinuumGreenIdentityRetained.TraceVanishingCompactSupportOrDecay
      (scalarKineticBoundaryProblemOfPair pair) f :=
  witness.trace_vanishing_of_decay f hf

/--
003A1 readout.  The differentiable-function-space witness surface exists, but
concrete calculus semantics and the remaining 003A bundle fields are retained.
-/
def phase1Blocker003A1DifferentiableFunctionSpaceV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .dischargedConditional
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after the 003A1 witness-surface increment. -/
theorem phase1_blocker003a1_function_space_v0_phase2_not_authorized :
    ¬ phase1Blocker003A1DifferentiableFunctionSpaceV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumDifferentiableFunctionSpace
end QFT
end ToeFormal
