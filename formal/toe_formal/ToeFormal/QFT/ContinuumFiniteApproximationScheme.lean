/-
ToeFormal/QFT/ContinuumFiniteApproximationScheme.lean

Finite approximation scheme surface for
PHASE1-BLOCKER-003A1A1C1_APPROXIMATION_SCHEME_RETAINED.

Scope:
- refine the first finite-to-continuum lift obligation into a concrete object
  shape
- name the finite refinement parameter and finite domain family
- name the continuum target domain, approximation map, reconstruction map,
  refinement relation, and convergence meaning
- prove only structural projection lemmas about a supplied scheme
- do not claim integral convergence, operator convergence, boundary-trace
  convergence, Green-identity preservation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumFiniteToContinuumLift

namespace ToeFormal
namespace QFT
namespace ContinuumFiniteApproximationScheme

open ContinuumFirstVariation
open ContinuumAnalyticBlocker003
open ContinuumFiniteToContinuumLift
set_option autoImplicit false

noncomputable section

/-- Retained id for the approximation-scheme sub-blocker. -/
def phase1Blocker003A1A1C1ApproximationSchemeRetainedId : String :=
  "PHASE1-BLOCKER-003A1A1C1_APPROXIMATION_SCHEME_RETAINED"

/-- The parent lift object targeted by this narrower approximation-scheme slice. -/
def phase1Blocker003A1A1C1TargetsLiftObject :
    Phase1Blocker003A1A1CFiniteToContinuumLiftMissingObject :=
  .limitingDomainSequenceOrApproximationMap

/-- Expected lift object for the approximation-scheme sub-blocker. -/
def phase1Blocker003A1A1C1ExpectedLiftObject :
    Phase1Blocker003A1A1CFiniteToContinuumLiftMissingObject :=
  .limitingDomainSequenceOrApproximationMap

/-- Missing objects for an actual finite approximation scheme. -/
inductive Phase1Blocker003A1A1C1ApproximationSchemeMissingObject where
  | finiteIndexDomainFamily
  | continuumTargetDomain
  | approximationMap
  | reconstructionMap
  | refinementOrLimitParameter
  | convergenceMeaning
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained approximation-scheme objects. -/
def phase1Blocker003A1A1C1ApproximationSchemeMissingObjectId :
    Phase1Blocker003A1A1C1ApproximationSchemeMissingObject → String
  | .finiteIndexDomainFamily =>
      "003A1A1C1_FINITE_INDEX_DOMAIN_FAMILY_RETAINED"
  | .continuumTargetDomain =>
      "003A1A1C1_CONTINUUM_TARGET_DOMAIN_RETAINED"
  | .approximationMap =>
      "003A1A1C1_APPROXIMATION_MAP_RETAINED"
  | .reconstructionMap =>
      "003A1A1C1_RECONSTRUCTION_MAP_RETAINED"
  | .refinementOrLimitParameter =>
      "003A1A1C1_REFINEMENT_OR_LIMIT_PARAMETER_RETAINED"
  | .convergenceMeaning =>
      "003A1A1C1_CONVERGENCE_MEANING_RETAINED"

/-- Exact retained objects for the approximation-scheme slice. -/
def phase1Blocker003A1A1C1ApproximationSchemeMissingObjectsV0 :
    List Phase1Blocker003A1A1C1ApproximationSchemeMissingObject :=
  [ .finiteIndexDomainFamily
  , .continuumTargetDomain
  , .approximationMap
  , .reconstructionMap
  , .refinementOrLimitParameter
  , .convergenceMeaning
  ]

/-- The approximation-scheme retained-object list is explicit. -/
theorem phase1_blocker003a1a1c1_approximation_scheme_missing_objects_v0_expected :
    phase1Blocker003A1A1C1ApproximationSchemeMissingObjectsV0 =
      [ .finiteIndexDomainFamily
      , .continuumTargetDomain
      , .approximationMap
      , .reconstructionMap
      , .refinementOrLimitParameter
      , .convergenceMeaning
      ] := by
  rfl

/--
A bounded finite approximation scheme shape.

The scheme is intentionally structural: it says what data would connect a
family of finite domains to a continuum target.  The field `convergenceMeaning`
is only the proposition that later convergence work must prove.
-/
structure FiniteApproximationScheme (ContinuumPoint : Type) where
  RefinementParameter : Type
  FiniteDomain : RefinementParameter → Type
  finiteDomainFintype : (r : RefinementParameter) → Fintype (FiniteDomain r)
  samplePoint : (r : RefinementParameter) → FiniteDomain r → ContinuumPoint
  approximationMap :
    (r : RefinementParameter) →
      ContinuumField ContinuumPoint → ContinuumField (FiniteDomain r)
  reconstructionMap :
    (r : RefinementParameter) →
      ContinuumField (FiniteDomain r) → ContinuumField ContinuumPoint
  refinementRelation : RefinementParameter → RefinementParameter → Prop
  convergenceMeaning : Prop

/-- A supplied scheme has a finite domain at every refinement parameter. -/
theorem finite_approximation_scheme_finite_domain_family
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter) :
    Nonempty (Fintype (scheme.FiniteDomain r)) := by
  exact ⟨scheme.finiteDomainFintype r⟩

/-- A supplied scheme exposes its approximation map. -/
theorem finite_approximation_scheme_approximation_map_available
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter) :
    ∃ map :
      ContinuumField ContinuumPoint → ContinuumField (scheme.FiniteDomain r),
      map = scheme.approximationMap r := by
  exact ⟨scheme.approximationMap r, rfl⟩

/-- A supplied scheme exposes its reconstruction map. -/
theorem finite_approximation_scheme_reconstruction_map_available
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter) :
    ∃ map :
      ContinuumField (scheme.FiniteDomain r) → ContinuumField ContinuumPoint,
      map = scheme.reconstructionMap r := by
  exact ⟨scheme.reconstructionMap r, rfl⟩

/--
Witness for proving the convergence meaning attached to a scheme.

The current slice defines this witness shape but does not construct one.
-/
structure FiniteApproximationSchemeConvergenceWitness
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint) where
  convergence_meaning_supplied : scheme.convergenceMeaning

/-- A convergence witness supplies exactly the scheme's convergence meaning. -/
theorem finite_approximation_scheme_convergence_witness_supplies_meaning
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : FiniteApproximationSchemeConvergenceWitness scheme) :
    scheme.convergenceMeaning :=
  witness.convergence_meaning_supplied

/-- Current repository status for the approximation-scheme sub-blocker. -/
structure FiniteApproximationSchemeStatus where
  approximation_scheme_surface_defined : Prop
  approximation_scheme_surface_defined_supplied :
    approximation_scheme_surface_defined
  approximation_scheme_closed : Prop
  approximation_scheme_not_closed : ¬ approximation_scheme_closed
  retained_blocker_id : String

/-- Current approximation-scheme status: object shape defined, actual scheme retained. -/
def finiteApproximationSchemeStatusV0 :
    FiniteApproximationSchemeStatus where
  approximation_scheme_surface_defined := True
  approximation_scheme_surface_defined_supplied := True.intro
  approximation_scheme_closed := False
  approximation_scheme_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C1ApproximationSchemeRetainedId

/-- The current status explicitly keeps the approximation scheme open. -/
theorem finite_approximation_scheme_status_v0_not_closed :
    ¬ finiteApproximationSchemeStatusV0.approximation_scheme_closed := by
  exact finiteApproximationSchemeStatusV0.approximation_scheme_not_closed

/-- The approximation-scheme slice targets the first finite-to-continuum lift object. -/
theorem phase1_blocker003a1a1c1_targets_lift_approximation_object :
    phase1Blocker003A1A1C1TargetsLiftObject =
      phase1Blocker003A1A1C1ExpectedLiftObject := by
  rfl

/--
003A1A1C1 readout.  The scheme shape is now named, but the actual finite
approximation scheme and all convergence-bearing lift facts remain retained.
-/
def phase1Blocker003A1A1C1ApproximationSchemeV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized while the approximation-scheme blocker is retained. -/
theorem phase1_blocker003a1a1c1_approximation_scheme_v0_phase2_not_authorized :
    ¬ phase1Blocker003A1A1C1ApproximationSchemeV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumFiniteApproximationScheme
end QFT
end ToeFormal
