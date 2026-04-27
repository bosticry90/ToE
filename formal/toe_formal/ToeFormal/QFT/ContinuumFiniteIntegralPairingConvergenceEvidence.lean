/-
ToeFormal/QFT/ContinuumFiniteIntegralPairingConvergenceEvidence.lean

Finite integral/pairing convergence evidence surface for
PHASE1-BLOCKER-003A1A1C3A_FINITE_INTEGRAL_PAIRING_CONVERGENCE_EVIDENCE_RETAINED.

Scope:
- split the first approximation-convergence witness evidence field
- record the finite weighted integral family and continuum pairing target
- state the finite integral/pairing convergence proposition
- connect supplied evidence to the approximation-convergence witness field
- prove only conditional wiring lemmas
- do not prove analytic integral or pairing convergence
- do not claim Green identity discharge, operator-domain closure, integration
  regularity, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumApproximationConvergenceWitness

namespace ToeFormal
namespace QFT
namespace ContinuumFiniteIntegralPairingConvergenceEvidence

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumFiniteWeightedIntegralModel
open ContinuumApproximationConvergenceContract
open ContinuumApproximationConvergenceWitness
set_option autoImplicit false

noncomputable section

/-- Retained id for finite integral/pairing convergence evidence. -/
def phase1Blocker003A1A1C3AFiniteIntegralPairingConvergenceEvidenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3A_FINITE_INTEGRAL_PAIRING_CONVERGENCE_EVIDENCE_RETAINED"

/-- The witness object targeted by this evidence slice. -/
def phase1Blocker003A1A1C3ATargetsWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .finiteIntegralPairingEvidence

/-- Expected witness object for this evidence slice. -/
def phase1Blocker003A1A1C3AExpectedWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .finiteIntegralPairingEvidence

/-- Missing objects for actual finite integral/pairing convergence evidence. -/
inductive Phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObject where
  | finiteWeightedIntegralFamily
  | continuumPairingTarget
  | sampledFieldPairingStatement
  | finiteIntegralPairingLimitStatement
  | contractFieldLink
  | analyticConvergenceEvidence
deriving DecidableEq, Repr

/-- Machine-facing ids for retained finite integral/pairing evidence objects. -/
def phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObjectId :
    Phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObject -> String
  | .finiteWeightedIntegralFamily =>
      "003A1A1C3A_FINITE_WEIGHTED_INTEGRAL_FAMILY_RETAINED"
  | .continuumPairingTarget =>
      "003A1A1C3A_CONTINUUM_PAIRING_TARGET_RETAINED"
  | .sampledFieldPairingStatement =>
      "003A1A1C3A_SAMPLED_FIELD_PAIRING_STATEMENT_RETAINED"
  | .finiteIntegralPairingLimitStatement =>
      "003A1A1C3A_FINITE_INTEGRAL_PAIRING_LIMIT_STATEMENT_RETAINED"
  | .contractFieldLink =>
      "003A1A1C3A_CONTRACT_FIELD_LINK_RETAINED"
  | .analyticConvergenceEvidence =>
      "003A1A1C3A_ANALYTIC_CONVERGENCE_EVIDENCE_RETAINED"

/-- Exact retained objects for finite integral/pairing convergence evidence. -/
def phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObjectsV0 :
    List Phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObject :=
  [ .finiteWeightedIntegralFamily
  , .continuumPairingTarget
  , .sampledFieldPairingStatement
  , .finiteIntegralPairingLimitStatement
  , .contractFieldLink
  , .analyticConvergenceEvidence
  ]

/-- The retained-object list for this evidence field is explicit. -/
theorem phase1_blocker003a1a1c3a_missing_objects_v0_expected :
    phase1Blocker003A1A1C3AFiniteIntegralPairingMissingObjectsV0 =
      [ .finiteWeightedIntegralFamily
      , .continuumPairingTarget
      , .sampledFieldPairingStatement
      , .finiteIntegralPairingLimitStatement
      , .contractFieldLink
      , .analyticConvergenceEvidence
      ] := by
  rfl

/-- Finite weighted integral induced by a scheme-level weight family. -/
def finiteWeightedIntegralOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (f : ContinuumField (scheme.FiniteDomain r)) : Real :=
  letI : Fintype (scheme.FiniteDomain r) := scheme.finiteDomainFintype r
  finiteWeightedIntegral { weight := weight r } f

/-- Finite weighted pairing induced by a scheme-level weight family. -/
def finiteWeightedPairingOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField (scheme.FiniteDomain r)) : Real :=
  letI : Fintype (scheme.FiniteDomain r) := scheme.finiteDomainFintype r
  finiteWeightedPairing { weight := weight r } x y

/-- The scheme-level finite pairing is the continuum pairing for its finite integral. -/
theorem finite_weighted_scheme_pairing_eq_continuum_pair
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (weight :
      (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real)
    (r : scheme.RefinementParameter)
    (x y : ContinuumField (scheme.FiniteDomain r)) :
    finiteWeightedPairingOfScheme scheme weight r x y =
      ContinuumPair (finiteWeightedIntegralOfScheme scheme weight r) x y := by
  rfl

/--
Focused evidence object for the finite integral/pairing convergence field.

The convergence statement is intentionally a proposition supplied by the caller.
This surface records the finite weighted side, the continuum target integral,
and the link from that statement into the contract field.
-/
structure FiniteIntegralPairingConvergenceEvidence
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (contract : ApproximationConvergenceContract scheme) where
  finiteWeight :
    (r : scheme.RefinementParameter) -> scheme.FiniteDomain r -> Real
  continuumIntegral : ContinuumField ContinuumPoint -> Real
  finite_integral_pairing_convergence_statement : Prop
  finite_integral_pairing_convergence_statement_supplied :
    finite_integral_pairing_convergence_statement
  statement_supplies_contract_field :
    finite_integral_pairing_convergence_statement ->
      contract.finite_integral_pairing_to_continuum_pairing

/-- Supplied finite integral/pairing evidence fills the contract field. -/
theorem finite_integral_pairing_evidence_supplies_contract_field
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      FiniteIntegralPairingConvergenceEvidence scheme contract) :
    contract.finite_integral_pairing_to_continuum_pairing :=
  evidence.statement_supplies_contract_field
    evidence.finite_integral_pairing_convergence_statement_supplied

/--
Build the full approximation-convergence witness when this finite evidence
and the remaining four evidence fields are supplied.
-/
def approximationConvergenceWitnessOfFiniteIntegralPairingEvidence
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      FiniteIntegralPairingConvergenceEvidence scheme contract)
    (reconstructed :
      contract.reconstructed_field_to_continuum_field)
    (operatorAction :
      contract.operator_action_under_discretization_to_continuum_operator)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceWitness ContinuumPoint where
  scheme := scheme
  contract := contract
  finite_integral_pairing_to_continuum_pairing_supplied :=
    finite_integral_pairing_evidence_supplies_contract_field evidence
  reconstructed_field_to_continuum_field_supplied := reconstructed
  operator_action_under_discretization_to_continuum_operator_supplied :=
    operatorAction
  boundary_trace_approximation_supplied := boundaryTrace
  green_identity_compatibility_supplied := greenIdentity

/-- The witness built from finite evidence satisfies the convergence contract. -/
theorem finite_integral_pairing_evidence_builds_contract_witness
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      FiniteIntegralPairingConvergenceEvidence scheme contract)
    (reconstructed :
      contract.reconstructed_field_to_continuum_field)
    (operatorAction :
      contract.operator_action_under_discretization_to_continuum_operator)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceContractClosed contract := by
  exact approximation_convergence_witness_satisfies_contract
    (approximationConvergenceWitnessOfFiniteIntegralPairingEvidence
      evidence reconstructed operatorAction boundaryTrace greenIdentity)

/-- Current repository status for finite integral/pairing convergence evidence. -/
structure FiniteIntegralPairingConvergenceEvidenceStatus where
  evidence_surface_defined : Prop
  evidence_surface_defined_supplied : evidence_surface_defined
  analytic_finite_integral_pairing_convergence_closed : Prop
  analytic_finite_integral_pairing_convergence_not_closed :
    Not analytic_finite_integral_pairing_convergence_closed
  retained_blocker_id : String

/-- Current status: evidence shape defined, analytic convergence retained. -/
def finiteIntegralPairingConvergenceEvidenceStatusV0 :
    FiniteIntegralPairingConvergenceEvidenceStatus where
  evidence_surface_defined := True
  evidence_surface_defined_supplied := True.intro
  analytic_finite_integral_pairing_convergence_closed := False
  analytic_finite_integral_pairing_convergence_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C3AFiniteIntegralPairingConvergenceEvidenceRetainedId

/-- Short local status alias used by the readout theorem. -/
def evidenceStatusV0 : FiniteIntegralPairingConvergenceEvidenceStatus :=
  finiteIntegralPairingConvergenceEvidenceStatusV0

/-- The current status keeps finite integral/pairing convergence open. -/
theorem finite_integral_pairing_convergence_status_v0_not_closed :
    Not evidenceStatusV0.analytic_finite_integral_pairing_convergence_closed := by
  exact evidenceStatusV0.analytic_finite_integral_pairing_convergence_not_closed

/-- This slice targets the finite integral/pairing evidence field. -/
theorem phase1_blocker003a1a1c3a_targets_witness_field :
    phase1Blocker003A1A1C3ATargetsWitnessObject =
      phase1Blocker003A1A1C3AExpectedWitnessObject := by
  rfl

/--
003A1A1C3A readout.  The evidence field is named, but actual analytic finite
integral/pairing convergence remains retained.
-/
def phase1Blocker003A1A1C3AFiniteIntegralPairingEvidenceV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Short local phase readout alias used by the Phase 2 theorem. -/
def evidencePhaseReadoutV0 : Phase1Blocker003Split :=
  phase1Blocker003A1A1C3AFiniteIntegralPairingEvidenceV0

/-- Phase 2 remains unauthorized while this evidence field is retained. -/
theorem phase1_blocker003a1a1c3a_evidence_v0_phase2_not_authorized :
    Not evidencePhaseReadoutV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumFiniteIntegralPairingConvergenceEvidence
end QFT
end ToeFormal
