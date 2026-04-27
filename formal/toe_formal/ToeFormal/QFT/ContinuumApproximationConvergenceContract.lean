/-
ToeFormal/QFT/ContinuumApproximationConvergenceContract.lean

Approximation convergence contract surface for
PHASE1-BLOCKER-003A1A1C2_APPROXIMATION_CONVERGENCE_CONTRACT_RETAINED.

Scope:
- refine the convergence meaning of a finite approximation scheme into named
  contract clauses
- state finite integral/pairing, reconstruction, operator-action,
  boundary-trace, and Green-identity compatibility obligations
- prove only conditional projection lemmas about a supplied contract witness
- do not prove any analytic convergence theorem
- do not claim Green identity discharge, operator-domain closure, integration
  regularity, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumFiniteApproximationScheme

namespace ToeFormal
namespace QFT
namespace ContinuumApproximationConvergenceContract

open ContinuumAnalyticBlocker003
open ContinuumFiniteApproximationScheme
set_option autoImplicit false

noncomputable section

/-- Retained id for the approximation-convergence contract blocker. -/
def phase1Blocker003A1A1C2ApproximationConvergenceContractRetainedId : String :=
  "PHASE1-BLOCKER-003A1A1C2_APPROXIMATION_CONVERGENCE_CONTRACT_RETAINED"

/-- The approximation-scheme object targeted by this convergence-contract slice. -/
def phase1Blocker003A1A1C2TargetsApproximationObject :
    Phase1Blocker003A1A1C1ApproximationSchemeMissingObject :=
  .convergenceMeaning

/-- Expected approximation-scheme object for this slice. -/
def phase1Blocker003A1A1C2ExpectedApproximationObject :
    Phase1Blocker003A1A1C1ApproximationSchemeMissingObject :=
  .convergenceMeaning

/-- Missing objects for a real approximation-convergence contract. -/
inductive Phase1Blocker003A1A1C2ApproximationConvergenceMissingObject where
  | finiteIntegralPairingConvergence
  | reconstructedFieldConvergence
  | operatorActionConvergence
  | boundaryTraceApproximation
  | greenIdentityCompatibility
  | schemeConvergenceMeaningLink
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained approximation-convergence objects. -/
def phase1Blocker003A1A1C2ApproximationConvergenceMissingObjectId :
    Phase1Blocker003A1A1C2ApproximationConvergenceMissingObject -> String
  | .finiteIntegralPairingConvergence =>
      "003A1A1C2_FINITE_INTEGRAL_PAIRING_CONVERGENCE_RETAINED"
  | .reconstructedFieldConvergence =>
      "003A1A1C2_RECONSTRUCTED_FIELD_CONVERGENCE_RETAINED"
  | .operatorActionConvergence =>
      "003A1A1C2_OPERATOR_ACTION_CONVERGENCE_RETAINED"
  | .boundaryTraceApproximation =>
      "003A1A1C2_BOUNDARY_TRACE_APPROXIMATION_RETAINED"
  | .greenIdentityCompatibility =>
      "003A1A1C2_GREEN_IDENTITY_COMPATIBILITY_RETAINED"
  | .schemeConvergenceMeaningLink =>
      "003A1A1C2_SCHEME_CONVERGENCE_MEANING_LINK_RETAINED"

/-- Exact retained objects for the approximation-convergence contract slice. -/
def phase1Blocker003A1A1C2ApproximationConvergenceMissingObjectsV0 :
    List Phase1Blocker003A1A1C2ApproximationConvergenceMissingObject :=
  [ .finiteIntegralPairingConvergence
  , .reconstructedFieldConvergence
  , .operatorActionConvergence
  , .boundaryTraceApproximation
  , .greenIdentityCompatibility
  , .schemeConvergenceMeaningLink
  ]

/-- The approximation-convergence retained-object list is explicit. -/
theorem phase1_blocker003a1a1c2_contract_missing_objects_v0_expected :
    phase1Blocker003A1A1C2ApproximationConvergenceMissingObjectsV0 =
      [ .finiteIntegralPairingConvergence
      , .reconstructedFieldConvergence
      , .operatorActionConvergence
      , .boundaryTraceApproximation
      , .greenIdentityCompatibility
      , .schemeConvergenceMeaningLink
      ] := by
  rfl

/--
A bounded convergence contract for a finite approximation scheme.

The clauses are propositions rather than constructed convergence theorems.
The final field explains how the five clauses would imply the scheme's
`convergenceMeaning` once they are actually supplied.
-/
structure ApproximationConvergenceContract
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint) where
  finite_integral_pairing_to_continuum_pairing : Prop
  reconstructed_field_to_continuum_field : Prop
  operator_action_under_discretization_to_continuum_operator : Prop
  boundary_trace_approximation : Prop
  green_identity_compatibility : Prop
  contract_implies_scheme_convergence :
    finite_integral_pairing_to_continuum_pairing ->
    reconstructed_field_to_continuum_field ->
    operator_action_under_discretization_to_continuum_operator ->
    boundary_trace_approximation ->
    green_identity_compatibility ->
    scheme.convergenceMeaning

/-- All clauses of an approximation-convergence contract are supplied. -/
def ApproximationConvergenceContractClosed
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (contract : ApproximationConvergenceContract scheme) : Prop :=
  contract.finite_integral_pairing_to_continuum_pairing /\
    contract.reconstructed_field_to_continuum_field /\
    contract.operator_action_under_discretization_to_continuum_operator /\
    contract.boundary_trace_approximation /\
    contract.green_identity_compatibility

/-- Witness package for a completed approximation-convergence contract. -/
structure ApproximationConvergenceContractWitness
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint} where
  contract : ApproximationConvergenceContract scheme
  finite_integral_pairing_to_continuum_pairing_supplied :
    contract.finite_integral_pairing_to_continuum_pairing
  reconstructed_field_to_continuum_field_supplied :
    contract.reconstructed_field_to_continuum_field
  operator_action_under_discretization_to_continuum_operator_supplied :
    contract.operator_action_under_discretization_to_continuum_operator
  boundary_trace_approximation_supplied :
    contract.boundary_trace_approximation
  green_identity_compatibility_supplied :
    contract.green_identity_compatibility

/-- A supplied contract witness closes the contract clauses. -/
theorem approximation_convergence_contract_witness_supplies_closed
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    ApproximationConvergenceContractClosed witness.contract := by
  exact
    ⟨ witness.finite_integral_pairing_to_continuum_pairing_supplied
    , witness.reconstructed_field_to_continuum_field_supplied
    , witness.operator_action_under_discretization_to_continuum_operator_supplied
    , witness.boundary_trace_approximation_supplied
    , witness.green_identity_compatibility_supplied
    ⟩

/-- A supplied contract witness includes finite integral/pairing convergence. -/
theorem approximation_contract_witness_finite_integral_pairing
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    witness.contract.finite_integral_pairing_to_continuum_pairing :=
  witness.finite_integral_pairing_to_continuum_pairing_supplied

/-- A supplied contract witness includes reconstructed-field convergence. -/
theorem approximation_contract_witness_reconstructed_field
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    witness.contract.reconstructed_field_to_continuum_field :=
  witness.reconstructed_field_to_continuum_field_supplied

/-- A supplied contract witness includes operator-action convergence. -/
theorem approximation_contract_witness_operator_action
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    witness.contract.operator_action_under_discretization_to_continuum_operator :=
  witness.operator_action_under_discretization_to_continuum_operator_supplied

/-- A supplied contract witness includes boundary-trace approximation. -/
theorem approximation_contract_witness_boundary_trace
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    witness.contract.boundary_trace_approximation :=
  witness.boundary_trace_approximation_supplied

/-- A supplied contract witness includes Green-identity compatibility. -/
theorem approximation_contract_witness_green_identity
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    witness.contract.green_identity_compatibility :=
  witness.green_identity_compatibility_supplied

/-- A supplied contract witness implies the scheme's convergence meaning. -/
theorem approximation_contract_witness_supplies_scheme_meaning
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    (witness : ApproximationConvergenceContractWitness (scheme := scheme)) :
    scheme.convergenceMeaning :=
  witness.contract.contract_implies_scheme_convergence
    witness.finite_integral_pairing_to_continuum_pairing_supplied
    witness.reconstructed_field_to_continuum_field_supplied
    witness.operator_action_under_discretization_to_continuum_operator_supplied
    witness.boundary_trace_approximation_supplied
    witness.green_identity_compatibility_supplied

/-- Current repository status for the approximation-convergence contract. -/
structure ApproximationConvergenceContractStatus where
  convergence_contract_surface_defined : Prop
  convergence_contract_surface_defined_supplied :
    convergence_contract_surface_defined
  convergence_contract_closed : Prop
  convergence_contract_not_closed : Not convergence_contract_closed
  retained_blocker_id : String

/-- Current status: contract shape defined, actual convergence contract retained. -/
def approximationConvergenceContractStatusV0 :
    ApproximationConvergenceContractStatus where
  convergence_contract_surface_defined := True
  convergence_contract_surface_defined_supplied := True.intro
  convergence_contract_closed := False
  convergence_contract_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C2ApproximationConvergenceContractRetainedId

/-- The current status explicitly keeps the convergence contract open. -/
theorem approximation_convergence_contract_status_v0_not_closed :
    Not approximationConvergenceContractStatusV0.convergence_contract_closed := by
  exact approximationConvergenceContractStatusV0.convergence_contract_not_closed

/-- This slice targets the scheme's convergence-meaning object. -/
theorem phase1_blocker003a1a1c2_targets_scheme_convergence_meaning :
    phase1Blocker003A1A1C2TargetsApproximationObject =
      phase1Blocker003A1A1C2ExpectedApproximationObject := by
  rfl

/--
003A1A1C2 readout.  The convergence contract is named, but all convergence
clauses and the full finite-to-continuum lift remain retained.
-/
def phase1Blocker003A1A1C2ApproximationConvergenceContractV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized while the convergence contract is retained. -/
theorem phase1_blocker003a1a1c2_contract_v0_phase2_not_authorized :
    Not phase1Blocker003A1A1C2ApproximationConvergenceContractV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumApproximationConvergenceContract
end QFT
end ToeFormal
