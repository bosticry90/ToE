/-
ToeFormal/QFT/ContinuumFiniteIntegralPairingConvergenceAttempt.lean

Bounded discharge attempt for the A evidence field:
finite integral/pairing convergence.

Scope:
- prove the finite-side sampled weighted pairing identity available from the
  finite weighted model
- isolate the remaining finite-to-continuum limit evidence as a narrower
  retained blocker
- conditionally package a full finite integral/pairing convergence evidence
  object only when the retained limit evidence is supplied
- do not prove analytic convergence, Green identity discharge, continuum
  closure, operator-domain closure, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumFiniteIntegralPairingConvergenceEvidence

namespace ToeFormal
namespace QFT
namespace ContinuumFiniteIntegralPairingConvergenceAttempt

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumApproximationConvergenceContract
open ContinuumFiniteIntegralPairingConvergenceEvidence
set_option autoImplicit false

noncomputable section

/-- Narrow retained id for the actual finite-to-continuum pairing limit. -/
def phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitRetainedId : String :=
  "PHASE1-BLOCKER-003A1A1C3A1_FINITE_INTEGRAL_PAIRING_LIMIT_RETAINED"

/-- Machine-facing outcome id for this bounded attempt. -/
def finiteIntegralPairingConvergenceAttemptOutcomeId : String :=
  "FINITE_INTEGRAL_PAIRING_CONVERGENCE_ATTEMPT_FINITE_SIDE_DISCHARGED_LIMIT_RETAINED"

/-- Remaining objects for the actual finite integral/pairing limit theorem. -/
inductive Phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObject where
  | continuumPairingLimitTopology
  | refinementLimitFilter
  | finiteWeightMeasureConvergence
  | sampledFieldIntegrability
  | finitePairingLimitTheorem
  | contractFieldEvidence
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained limit-theorem objects. -/
def phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObjectId :
    Phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObject -> String
  | .continuumPairingLimitTopology =>
      "003A1A1C3A1_CONTINUUM_PAIRING_LIMIT_TOPOLOGY_RETAINED"
  | .refinementLimitFilter =>
      "003A1A1C3A1_REFINEMENT_LIMIT_FILTER_RETAINED"
  | .finiteWeightMeasureConvergence =>
      "003A1A1C3A1_FINITE_WEIGHT_MEASURE_CONVERGENCE_RETAINED"
  | .sampledFieldIntegrability =>
      "003A1A1C3A1_SAMPLED_FIELD_INTEGRABILITY_RETAINED"
  | .finitePairingLimitTheorem =>
      "003A1A1C3A1_FINITE_PAIRING_LIMIT_THEOREM_RETAINED"
  | .contractFieldEvidence =>
      "003A1A1C3A1_CONTRACT_FIELD_EVIDENCE_RETAINED"

/-- Exact retained object list for the narrowed limit theorem. -/
def phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObjectsV0 :
    List Phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObject :=
  [ .continuumPairingLimitTopology
  , .refinementLimitFilter
  , .finiteWeightMeasureConvergence
  , .sampledFieldIntegrability
  , .finitePairingLimitTheorem
  , .contractFieldEvidence
  ]

/-- The retained limit-theorem object list is explicit. -/
theorem phase1_blocker003a1a1c3a1_limit_missing_objects_v0_expected :
    phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitMissingObjectsV0 =
      [ .continuumPairingLimitTopology
      , .refinementLimitFilter
      , .finiteWeightMeasureConvergence
      , .sampledFieldIntegrability
      , .finitePairingLimitTheorem
      , .contractFieldEvidence
      ] := by
  rfl

/-- Sampled finite weighted pairing at a refinement parameter. -/
def sampledFiniteWeightedPairingOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField ContinuumPoint) : Real :=
  finiteWeightedPairingOfScheme scheme weight r
    (scheme.approximationMap r x) (scheme.approximationMap r y)

/-- Sampled finite product integral at a refinement parameter. -/
def sampledFiniteWeightedProductIntegralOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField ContinuumPoint) : Real :=
  finiteWeightedIntegralOfScheme scheme weight r
    (fun p => scheme.approximationMap r x p * scheme.approximationMap r y p)

/-- The sampled finite pairing is the finite weighted product integral. -/
theorem sampled_finite_weighted_pairing_eq_product_integral
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField ContinuumPoint) :
    sampledFiniteWeightedPairingOfScheme scheme weight r x y =
      sampledFiniteWeightedProductIntegralOfScheme scheme weight r x y := by
  rfl

/--
Finite-side discharge: sampled finite weighted pairing is the `ContinuumPair`
for the finite weighted integral at each refinement.
-/
theorem sampled_finite_weighted_pairing_eq_continuum_pair_of_finite_integral
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField ContinuumPoint) :
    sampledFiniteWeightedPairingOfScheme scheme weight r x y =
      ContinuumPair (finiteWeightedIntegralOfScheme scheme weight r)
        (scheme.approximationMap r x) (scheme.approximationMap r y) := by
  exact finite_weighted_scheme_pairing_eq_continuum_pair scheme weight r
    (scheme.approximationMap r x) (scheme.approximationMap r y)

/-- Finite-side identity closed by the attempt. -/
def FiniteIntegralPairingFiniteSideIdentity
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real) :
    Prop :=
  ∀ (r : scheme.RefinementParameter) (x y : ContinuumField ContinuumPoint),
    sampledFiniteWeightedPairingOfScheme scheme weight r x y =
      ContinuumPair (finiteWeightedIntegralOfScheme scheme weight r)
        (scheme.approximationMap r x) (scheme.approximationMap r y)

/-- The finite-side identity is mechanically discharged for any scheme weights. -/
theorem finite_integral_pairing_attempt_finite_side_identity_closed
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real) :
    FiniteIntegralPairingFiniteSideIdentity scheme weight := by
  intro r x y
  exact sampled_finite_weighted_pairing_eq_continuum_pair_of_finite_integral
    scheme weight r x y

/--
Retained limit evidence needed to turn the finite-side identity into the A
field of the approximation-convergence contract.
-/
structure FiniteIntegralPairingLimitEvidence
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (contract : ApproximationConvergenceContract scheme) where
  finiteWeight :
    (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real
  continuumIntegral : ContinuumField ContinuumPoint -> Real
  finite_side_identity :
    FiniteIntegralPairingFiniteSideIdentity scheme finiteWeight
  finite_integral_pairing_limit_statement : Prop
  finite_integral_pairing_limit_statement_supplied :
    finite_integral_pairing_limit_statement
  limit_statement_supplies_contract_field :
    finite_integral_pairing_limit_statement ->
      contract.finite_integral_pairing_to_continuum_pairing

/--
If the retained limit evidence is supplied, it becomes the existing A-field
finite integral/pairing convergence evidence.
-/
def finiteIntegralPairingEvidenceOfLimitEvidence
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence : FiniteIntegralPairingLimitEvidence scheme contract) :
    FiniteIntegralPairingConvergenceEvidence scheme contract where
  finiteWeight := evidence.finiteWeight
  continuumIntegral := evidence.continuumIntegral
  finite_integral_pairing_convergence_statement :=
    evidence.finite_integral_pairing_limit_statement
  finite_integral_pairing_convergence_statement_supplied :=
    evidence.finite_integral_pairing_limit_statement_supplied
  statement_supplies_contract_field :=
    evidence.limit_statement_supplies_contract_field

/-- Supplied retained limit evidence fills the A contract field. -/
theorem finite_integral_pairing_limit_evidence_supplies_contract_field
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence : FiniteIntegralPairingLimitEvidence scheme contract) :
    contract.finite_integral_pairing_to_continuum_pairing := by
  exact finite_integral_pairing_evidence_supplies_contract_field
    (finiteIntegralPairingEvidenceOfLimitEvidence evidence)

/-- Status for the bounded A-field discharge attempt. -/
structure FiniteIntegralPairingConvergenceAttemptStatus where
  finite_side_pairing_identity_closed : Prop
  finite_side_pairing_identity_closed_supplied :
    finite_side_pairing_identity_closed
  analytic_limit_to_continuum_pairing_closed : Prop
  analytic_limit_to_continuum_pairing_not_closed :
    Not analytic_limit_to_continuum_pairing_closed
  full_a_evidence_closed : Prop
  full_a_evidence_not_closed : Not full_a_evidence_closed
  retained_limit_blocker_id : String
  parent_evidence_blocker_id : String
  outcome_id : String

/--
Current attempt status: finite-side identity closed, actual limit evidence and
full A-field evidence retained.
-/
def finiteIntegralPairingConvergenceAttemptStatusV0 :
    FiniteIntegralPairingConvergenceAttemptStatus where
  finite_side_pairing_identity_closed := True
  finite_side_pairing_identity_closed_supplied := True.intro
  analytic_limit_to_continuum_pairing_closed := False
  analytic_limit_to_continuum_pairing_not_closed := by
    intro h
    exact h
  full_a_evidence_closed := False
  full_a_evidence_not_closed := by
    intro h
    exact h
  retained_limit_blocker_id :=
    phase1Blocker003A1A1C3A1FiniteIntegralPairingLimitRetainedId
  parent_evidence_blocker_id :=
    phase1Blocker003A1A1C3AFiniteIntegralPairingConvergenceEvidenceRetainedId
  outcome_id :=
    finiteIntegralPairingConvergenceAttemptOutcomeId

/-- Short local status alias. -/
def attemptStatusV0 : FiniteIntegralPairingConvergenceAttemptStatus :=
  finiteIntegralPairingConvergenceAttemptStatusV0

/-- The bounded attempt closes only the finite-side sampled pairing identity. -/
theorem finite_integral_pairing_convergence_attempt_finite_side_closed_v0 :
    attemptStatusV0.finite_side_pairing_identity_closed := by
  exact attemptStatusV0.finite_side_pairing_identity_closed_supplied

/-- The finite-to-continuum pairing limit remains retained. -/
theorem finite_integral_pairing_convergence_attempt_limit_not_closed_v0 :
    Not attemptStatusV0.analytic_limit_to_continuum_pairing_closed := by
  exact attemptStatusV0.analytic_limit_to_continuum_pairing_not_closed

/-- The full A evidence field remains retained after this bounded attempt. -/
theorem finite_integral_pairing_convergence_attempt_full_a_not_closed_v0 :
    Not attemptStatusV0.full_a_evidence_closed := by
  exact attemptStatusV0.full_a_evidence_not_closed

/-- The attempt exposes the expected outcome id. -/
theorem finite_integral_pairing_convergence_attempt_outcome_id_v0 :
    attemptStatusV0.outcome_id =
      finiteIntegralPairingConvergenceAttemptOutcomeId := by
  rfl

/--
003A1A1C3A1 readout.  The finite-side pairing identity is closed, but the
analytic finite-to-continuum integral/pairing limit remains retained.
-/
def phase1Blocker003A1A1C3A1FiniteIntegralPairingAttemptV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after this bounded A-field attempt. -/
theorem phase1_blocker003a1a1c3a1_attempt_v0_phase2_not_authorized :
    Not phase1Blocker003A1A1C3A1FiniteIntegralPairingAttemptV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumFiniteIntegralPairingConvergenceAttempt
end QFT
end ToeFormal
