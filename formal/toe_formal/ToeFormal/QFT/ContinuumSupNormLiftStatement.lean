/-
ToeFormal/QFT/ContinuumSupNormLiftStatement.lean

Bounded A1A1A1A2A2 finite-to-continuum sup norm lift statement.

Scope:
- state the finite-to-continuum lift needed after the finite-domain sup norm
  laws are discharged
- connect each refinement to the proved finite-domain sup-like candidate
- name the analytic structure still required for a continuum sup norm lift:
  reconstruction-map compatibility, pointwise/uniform convergence, continuum
  boundedness, sup convergence or dominance, and `ContinuumPair`
  compatibility
- record that the current model does not prove continuum sup convergence,
  construct a continuum sup norm, prove a pairing-limit theorem, or authorize
  Phase 2
-/

import ToeFormal.QFT.ContinuumPairingLimitFiniteDomainSupNorm

set_option linter.dupNamespace false

namespace ToeFormal
namespace QFT
namespace ContinuumSupNormLiftStatement

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumFiniteWeightedIntegralModel
open ContinuumPairingLimitAnalyticStructureSplit
open ContinuumPairingLimitFieldTopologyNorm
open ContinuumPairingLimitFiniteDomainSupNorm
open ContinuumPairingLimitSupLikeFieldNormCandidate
set_option autoImplicit false

noncomputable section

/-- Retained id for the finite-to-continuum sup norm lift statement. -/
def phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3A1A1A1A2A2_FINITE_TO_CONTINUUM_SUP_NORM_LIFT_RETAINED"

/-- Machine-facing outcome id for this bounded lift-statement slice. -/
def continuumSupNormLiftStatementOutcomeId : String :=
  "FINITE_TO_CONTINUUM_SUP_NORM_LIFT_STATEMENT_RECORDED_RETAINED"

/-- Parent continuum-sup blocker narrowed by this statement slice. -/
def phase1Blocker003A1A1C3A1A1A1A2A2ParentContinuumSupBlockerId :
    String :=
  phase1Blocker003A1A1C3A1A1A1A2A1ContinuumSupNormRetainedId

/-- Missing analytic objects for a finite-to-continuum sup norm lift. -/
inductive Phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObject where
  | continuumSupNormDefinition
  | reconstructionMapCompatibility
  | pointwiseOrUniformConvergence
  | continuumBoundedness
  | supConvergenceOrDominance
  | continuumPairCompatibility
deriving DecidableEq, Repr

/-- Machine-facing retained ids for finite-to-continuum sup norm lift objects. -/
def phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObjectId :
    Phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObject ->
      String
  | .continuumSupNormDefinition =>
      "003A1A1C3A1A1A1A2A2_CONTINUUM_SUP_NORM_DEFINITION_RETAINED"
  | .reconstructionMapCompatibility =>
      "003A1A1C3A1A1A1A2A2_RECONSTRUCTION_MAP_COMPATIBILITY_RETAINED"
  | .pointwiseOrUniformConvergence =>
      "003A1A1C3A1A1A1A2A2_POINTWISE_OR_UNIFORM_CONVERGENCE_RETAINED"
  | .continuumBoundedness =>
      "003A1A1C3A1A1A1A2A2_CONTINUUM_BOUNDEDNESS_RETAINED"
  | .supConvergenceOrDominance =>
      "003A1A1C3A1A1A1A2A2_SUP_CONVERGENCE_OR_DOMINANCE_RETAINED"
  | .continuumPairCompatibility =>
      "003A1A1C3A1A1A1A2A2_CONTINUUM_PAIR_COMPATIBILITY_RETAINED"

/-- Exact retained object list after this bounded lift statement. -/
def phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObjectsV0 :
    List Phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObject :=
  [ .continuumSupNormDefinition
  , .reconstructionMapCompatibility
  , .pointwiseOrUniformConvergence
  , .continuumBoundedness
  , .supConvergenceOrDominance
  , .continuumPairCompatibility
  ]

/-- The retained lift object list is explicit. -/
theorem phase1_blocker003a1a1c3a1a1a1a2a2_missing_objects_v0_expected :
    phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftMissingObjectsV0 =
      [ .continuumSupNormDefinition
      , .reconstructionMapCompatibility
      , .pointwiseOrUniformConvergence
      , .continuumBoundedness
      , .supConvergenceOrDominance
      , .continuumPairCompatibility
      ] := by
  rfl

/-- Reconstructed continuum field at one refinement. -/
def reconstructedContinuumFieldOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) :
    ContinuumField ContinuumPoint :=
  scheme.reconstructionMap r (scheme.approximationMap r field)

/-- Finite-domain sup norm value of sampled continuum data at one refinement. -/
def finiteSupNormOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteDomainNonempty :
      (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r))
    (finiteWeightDomain :
      (r : scheme.RefinementParameter) ->
        FiniteWeightedBaseDomain (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) : Real := by
  letI : Fintype (scheme.FiniteDomain r) := scheme.finiteDomainFintype r
  letI : Nonempty (scheme.FiniteDomain r) := finiteDomainNonempty r
  exact finiteDomainSupNorm
    (finiteWeightDomain r)
    (scheme.approximationMap r field)

/-- Finite-domain sup-like candidate at one refinement. -/
def finiteSupLikeCandidateAtRefinement
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteDomainNonempty :
      (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r))
    (finiteWeightDomain :
      (r : scheme.RefinementParameter) ->
        FiniteWeightedBaseDomain (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter) :
    SupLikeFieldNormCandidate (scheme.FiniteDomain r) := by
  letI : Fintype (scheme.FiniteDomain r) := scheme.finiteDomainFintype r
  letI : Nonempty (scheme.FiniteDomain r) := finiteDomainNonempty r
  exact finiteDomainSupLikeFieldNormCandidate (finiteWeightDomain r)

/-- Each refinement inherits the proved finite-domain sup-like norm laws. -/
theorem finite_sup_like_candidate_at_refinement_laws_supplied
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteDomainNonempty :
      (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r))
    (finiteWeightDomain :
      (r : scheme.RefinementParameter) ->
        FiniteWeightedBaseDomain (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter) :
    (finiteSupLikeCandidateAtRefinement
      scheme finiteDomainNonempty finiteWeightDomain r).sup_like_norm_laws := by
  letI : Fintype (scheme.FiniteDomain r) := scheme.finiteDomainFintype r
  letI : Nonempty (scheme.FiniteDomain r) := finiteDomainNonempty r
  exact finite_domain_sup_like_candidate_laws_supplied
    (finiteWeightDomain r)

/-- Continuum-pair compatibility required of a continuum sup norm. -/
def ContinuumSupNormPairCompatibility
    {ContinuumPoint : Type}
    (continuumSupNorm : ContinuumField ContinuumPoint -> Real)
    (continuumIntegral : ContinuumField ContinuumPoint -> Real) : Prop :=
  ∀ x y x' y' : ContinuumField ContinuumPoint,
    fieldDistanceOfNorm continuumSupNorm x x' = 0 ->
      fieldDistanceOfNorm continuumSupNorm y y' = 0 ->
        ContinuumPair continuumIntegral x y =
          ContinuumPair continuumIntegral x' y'

/-- Statement surface for lifting finite sup norms to a continuum sup norm. -/
structure ContinuumSupNormLiftStatement
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint) where
  finiteDomainNonempty :
    (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r)
  finiteWeightDomain :
    (r : scheme.RefinementParameter) ->
      FiniteWeightedBaseDomain (scheme.FiniteDomain r)
  continuumSupNorm : ContinuumField ContinuumPoint -> Real
  continuumIntegral : ContinuumField ContinuumPoint -> Real
  continuum_sup_norm_definition : Prop
  reconstruction_map_compatibility : Prop
  pointwise_or_uniform_convergence : Prop
  continuum_boundedness : Prop
  sup_convergence_or_dominance : Prop
  continuum_pair_compatibility : Prop
  continuum_pair_compatibility_def :
    continuum_pair_compatibility =
      ContinuumSupNormPairCompatibility continuumSupNorm continuumIntegral
  finite_to_continuum_sup_norm_statement : Prop
  statement_from_components :
    continuum_sup_norm_definition ->
      reconstruction_map_compatibility ->
        pointwise_or_uniform_convergence ->
          continuum_boundedness ->
            sup_convergence_or_dominance ->
              continuum_pair_compatibility ->
                finite_to_continuum_sup_norm_statement

/-- Supplied finite-to-continuum sup norm lift statement constructor. -/
def suppliedContinuumSupNormLiftStatement
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteDomainNonempty :
      (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r))
    (finiteWeightDomain :
      (r : scheme.RefinementParameter) ->
        FiniteWeightedBaseDomain (scheme.FiniteDomain r))
    (continuumSupNorm : ContinuumField ContinuumPoint -> Real)
    (continuumIntegral : ContinuumField ContinuumPoint -> Real)
    (continuumSupNormDefinition : Prop)
    (reconstructionMapCompatibility : Prop)
    (pointwiseOrUniformConvergence : Prop)
    (continuumBoundedness : Prop)
    (supConvergenceOrDominance : Prop) :
    ContinuumSupNormLiftStatement scheme where
  finiteDomainNonempty := finiteDomainNonempty
  finiteWeightDomain := finiteWeightDomain
  continuumSupNorm := continuumSupNorm
  continuumIntegral := continuumIntegral
  continuum_sup_norm_definition := continuumSupNormDefinition
  reconstruction_map_compatibility := reconstructionMapCompatibility
  pointwise_or_uniform_convergence := pointwiseOrUniformConvergence
  continuum_boundedness := continuumBoundedness
  sup_convergence_or_dominance := supConvergenceOrDominance
  continuum_pair_compatibility :=
    ContinuumSupNormPairCompatibility continuumSupNorm continuumIntegral
  continuum_pair_compatibility_def := rfl
  finite_to_continuum_sup_norm_statement :=
    continuumSupNormDefinition /\
      reconstructionMapCompatibility /\
        pointwiseOrUniformConvergence /\
          continuumBoundedness /\
            supConvergenceOrDominance /\
              ContinuumSupNormPairCompatibility
                continuumSupNorm continuumIntegral
  statement_from_components := by
    intro hSup hRecon hConv hBound hSupConv hPair
    exact ⟨hSup, hRecon, hConv, hBound, hSupConv, hPair⟩

/-- The supplied lift statement preserves the continuum sup norm. -/
theorem supplied_continuum_sup_norm_lift_statement_sup_norm_eq
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteDomainNonempty :
      (r : scheme.RefinementParameter) -> Nonempty (scheme.FiniteDomain r))
    (finiteWeightDomain :
      (r : scheme.RefinementParameter) ->
        FiniteWeightedBaseDomain (scheme.FiniteDomain r))
    (continuumSupNorm : ContinuumField ContinuumPoint -> Real)
    (continuumIntegral : ContinuumField ContinuumPoint -> Real)
    (continuumSupNormDefinition : Prop)
    (reconstructionMapCompatibility : Prop)
    (pointwiseOrUniformConvergence : Prop)
    (continuumBoundedness : Prop)
    (supConvergenceOrDominance : Prop) :
    (suppliedContinuumSupNormLiftStatement
      scheme
      finiteDomainNonempty
      finiteWeightDomain
      continuumSupNorm
      continuumIntegral
      continuumSupNormDefinition
      reconstructionMapCompatibility
      pointwiseOrUniformConvergence
      continuumBoundedness
      supConvergenceOrDominance).continuumSupNorm =
        continuumSupNorm := by
  rfl

/-- Evidence that all components of a sup norm lift statement are supplied. -/
structure ContinuumSupNormLiftEvidence
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (statement : ContinuumSupNormLiftStatement scheme) where
  continuum_sup_norm_definition_supplied :
    statement.continuum_sup_norm_definition
  reconstruction_map_compatibility_supplied :
    statement.reconstruction_map_compatibility
  pointwise_or_uniform_convergence_supplied :
    statement.pointwise_or_uniform_convergence
  continuum_boundedness_supplied :
    statement.continuum_boundedness
  sup_convergence_or_dominance_supplied :
    statement.sup_convergence_or_dominance
  continuum_pair_compatibility_supplied :
    statement.continuum_pair_compatibility

/-- Supplied lift evidence closes the statement proposition. -/
theorem continuum_sup_norm_lift_evidence_supplies_statement
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {statement : ContinuumSupNormLiftStatement scheme}
    (evidence : ContinuumSupNormLiftEvidence statement) :
    statement.finite_to_continuum_sup_norm_statement := by
  exact statement.statement_from_components
    evidence.continuum_sup_norm_definition_supplied
    evidence.reconstruction_map_compatibility_supplied
    evidence.pointwise_or_uniform_convergence_supplied
    evidence.continuum_boundedness_supplied
    evidence.sup_convergence_or_dominance_supplied
    evidence.continuum_pair_compatibility_supplied

/-- Current repository status for the finite-to-continuum sup norm lift. -/
structure ContinuumSupNormLiftStatementStatus where
  lift_statement_surface_defined : Prop
  lift_statement_surface_defined_supplied :
    lift_statement_surface_defined
  finite_sup_family_connected : Prop
  finite_sup_family_connected_supplied :
    finite_sup_family_connected
  analytic_components_named : Prop
  analytic_components_named_supplied : analytic_components_named
  continuum_sup_norm_lift_closed : Prop
  continuum_sup_norm_lift_not_closed :
    Not continuum_sup_norm_lift_closed
  continuum_sup_norm_closed : Prop
  continuum_sup_norm_not_closed : Not continuum_sup_norm_closed
  pairing_limit_theorem_closed : Prop
  pairing_limit_theorem_not_closed :
    Not pairing_limit_theorem_closed
  phase2Authorized : Bool
  retained_blocker_id : String
  parent_continuum_sup_blocker_id : String
  outcome_id : String

/--
Current status: the lift statement is recorded, but no continuum sup norm or
finite-to-continuum sup convergence theorem is supplied.
-/
def continuumSupNormLiftStatementStatusV0 :
    ContinuumSupNormLiftStatementStatus where
  lift_statement_surface_defined := True
  lift_statement_surface_defined_supplied := True.intro
  finite_sup_family_connected := True
  finite_sup_family_connected_supplied := True.intro
  analytic_components_named := True
  analytic_components_named_supplied := True.intro
  continuum_sup_norm_lift_closed := False
  continuum_sup_norm_lift_not_closed := by
    intro h
    exact h
  continuum_sup_norm_closed := False
  continuum_sup_norm_not_closed := by
    intro h
    exact h
  pairing_limit_theorem_closed := False
  pairing_limit_theorem_not_closed := by
    intro h
    exact h
  phase2Authorized := False
  retained_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftRetainedId
  parent_continuum_sup_blocker_id :=
    phase1Blocker003A1A1C3A1A1A1A2A2ParentContinuumSupBlockerId
  outcome_id := continuumSupNormLiftStatementOutcomeId

/-- Short local status alias. -/
def continuumSupNormLiftStatusV0 : ContinuumSupNormLiftStatementStatus :=
  continuumSupNormLiftStatementStatusV0

/-- The finite-to-continuum sup norm lift statement surface is defined. -/
theorem continuum_sup_norm_lift_statement_surface_defined_v0 :
    continuumSupNormLiftStatusV0.lift_statement_surface_defined := by
  exact continuumSupNormLiftStatusV0.lift_statement_surface_defined_supplied

/-- The finite sup norm family is connected to the statement surface. -/
theorem continuum_sup_norm_lift_finite_sup_family_connected_v0 :
    continuumSupNormLiftStatusV0.finite_sup_family_connected := by
  exact continuumSupNormLiftStatusV0.finite_sup_family_connected_supplied

/-- The required analytic components are named. -/
theorem continuum_sup_norm_lift_analytic_components_named_v0 :
    continuumSupNormLiftStatusV0.analytic_components_named := by
  exact continuumSupNormLiftStatusV0.analytic_components_named_supplied

/-- The finite-to-continuum sup norm lift theorem remains retained. -/
theorem continuum_sup_norm_lift_not_closed_v0 :
    Not continuumSupNormLiftStatusV0.continuum_sup_norm_lift_closed := by
  exact continuumSupNormLiftStatusV0.continuum_sup_norm_lift_not_closed

/-- Continuum sup norm construction remains retained. -/
theorem continuum_sup_norm_lift_continuum_sup_not_closed_v0 :
    Not continuumSupNormLiftStatusV0.continuum_sup_norm_closed := by
  exact continuumSupNormLiftStatusV0.continuum_sup_norm_not_closed

/-- The pairing-limit theorem remains retained. -/
theorem continuum_sup_norm_lift_pairing_limit_not_closed_v0 :
    Not continuumSupNormLiftStatusV0.pairing_limit_theorem_closed := by
  exact continuumSupNormLiftStatusV0.pairing_limit_theorem_not_closed

/-- The slice exposes the expected retained blocker id. -/
theorem continuum_sup_norm_lift_retained_id_v0 :
    continuumSupNormLiftStatusV0.retained_blocker_id =
      phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftRetainedId := by
  rfl

/-- The slice remains below the continuum-sup blocker. -/
theorem continuum_sup_norm_lift_parent_id_v0 :
    continuumSupNormLiftStatusV0.parent_continuum_sup_blocker_id =
      phase1Blocker003A1A1C3A1A1A1A2A1ContinuumSupNormRetainedId := by
  rfl

/-- The slice exposes the expected outcome id. -/
theorem continuum_sup_norm_lift_outcome_id_v0 :
    continuumSupNormLiftStatusV0.outcome_id =
      continuumSupNormLiftStatementOutcomeId := by
  rfl

/--
003A1A1C3A1A1A1A2A2 readout. The finite-to-continuum sup norm lift is stated,
but no analytic lift theorem or continuum sup norm is proved.
-/
def phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Short readout alias for parser-friendly field projection. -/
def continuumSupNormLiftReadoutV0 : Phase1Blocker003Split :=
  phase1Blocker003A1A1C3A1A1A1A2A2SupNormLiftV0

/-- Phase 2 remains unauthorized after this lift-statement slice. -/
theorem phase1_blocker003a1a1c3a1a1a1a2a2_sup_norm_lift_v0_phase2_not_authorized :
    Not continuumSupNormLiftReadoutV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumSupNormLiftStatement
end QFT
end ToeFormal
