/-
ToeFormal/QFT/ContinuumApproximationConvergenceWitness.lean

Approximation convergence witness surface for
PHASE1-BLOCKER-003A1A1C3_APPROXIMATION_CONVERGENCE_WITNESS_RETAINED.

Scope:
- record the chosen approximation scheme and convergence contract
- record the supplied evidence fields required by each convergence clause
- convert a supplied witness into the earlier contract-witness object
- prove only conditional projection lemmas from that supplied witness
- do not construct analytic convergence evidence
- do not claim Green identity discharge, operator-domain closure, integration
  regularity, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumApproximationConvergenceContract

namespace ToeFormal
namespace QFT
namespace ContinuumApproximationConvergenceWitness

open ContinuumAnalyticBlocker003
open ContinuumFiniteApproximationScheme
open ContinuumApproximationConvergenceContract
set_option autoImplicit false

noncomputable section

/-- Retained id for the approximation-convergence witness blocker. -/
def phase1Blocker003A1A1C3ApproximationConvergenceWitnessRetainedId : String :=
  "PHASE1-BLOCKER-003A1A1C3_APPROXIMATION_CONVERGENCE_WITNESS_RETAINED"

/-- The contract object targeted by this witness slice. -/
def phase1Blocker003A1A1C3TargetsContractObject :
    Phase1Blocker003A1A1C2ApproximationConvergenceMissingObject :=
  .schemeConvergenceMeaningLink

/-- Expected contract object for this witness slice. -/
def phase1Blocker003A1A1C3ExpectedContractObject :
    Phase1Blocker003A1A1C2ApproximationConvergenceMissingObject :=
  .schemeConvergenceMeaningLink

/-- Missing objects for an actual approximation-convergence witness. -/
inductive Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject where
  | chosenApproximationScheme
  | chosenConvergenceContract
  | finiteIntegralPairingEvidence
  | reconstructedFieldEvidence
  | operatorActionEvidence
  | boundaryTraceEvidence
  | greenIdentityCompatibilityEvidence
deriving DecidableEq, Repr

/-- Machine-facing ids for the retained approximation-convergence witness objects. -/
def phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObjectId :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject -> String
  | .chosenApproximationScheme =>
      "003A1A1C3_CHOSEN_APPROXIMATION_SCHEME_RETAINED"
  | .chosenConvergenceContract =>
      "003A1A1C3_CHOSEN_CONVERGENCE_CONTRACT_RETAINED"
  | .finiteIntegralPairingEvidence =>
      "003A1A1C3_FINITE_INTEGRAL_PAIRING_EVIDENCE_RETAINED"
  | .reconstructedFieldEvidence =>
      "003A1A1C3_RECONSTRUCTED_FIELD_EVIDENCE_RETAINED"
  | .operatorActionEvidence =>
      "003A1A1C3_OPERATOR_ACTION_EVIDENCE_RETAINED"
  | .boundaryTraceEvidence =>
      "003A1A1C3_BOUNDARY_TRACE_EVIDENCE_RETAINED"
  | .greenIdentityCompatibilityEvidence =>
      "003A1A1C3_GREEN_IDENTITY_COMPATIBILITY_EVIDENCE_RETAINED"

/-- Exact retained objects for the approximation-convergence witness slice. -/
def phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObjectsV0 :
    List Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  [ .chosenApproximationScheme
  , .chosenConvergenceContract
  , .finiteIntegralPairingEvidence
  , .reconstructedFieldEvidence
  , .operatorActionEvidence
  , .boundaryTraceEvidence
  , .greenIdentityCompatibilityEvidence
  ]

/-- The approximation-convergence witness retained-object list is explicit. -/
theorem phase1_blocker003a1a1c3_witness_missing_objects_v0_expected :
    phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObjectsV0 =
      [ .chosenApproximationScheme
      , .chosenConvergenceContract
      , .finiteIntegralPairingEvidence
      , .reconstructedFieldEvidence
      , .operatorActionEvidence
      , .boundaryTraceEvidence
      , .greenIdentityCompatibilityEvidence
      ] := by
  rfl

/--
Explicit witness for a chosen finite approximation scheme and convergence
contract.

The evidence fields are still propositions supplied by a caller; this surface
does not construct analytic evidence.
-/
structure ApproximationConvergenceWitness (ContinuumPoint : Type) where
  scheme : FiniteApproximationScheme ContinuumPoint
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

/-- A supplied explicit witness converts to the lower-level contract witness. -/
def contractWitnessOfApproximationConvergenceWitness
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    ApproximationConvergenceContractWitness (scheme := witness.scheme) where
  contract := witness.contract
  finite_integral_pairing_to_continuum_pairing_supplied :=
    witness.finite_integral_pairing_to_continuum_pairing_supplied
  reconstructed_field_to_continuum_field_supplied :=
    witness.reconstructed_field_to_continuum_field_supplied
  operator_action_under_discretization_to_continuum_operator_supplied :=
    witness.operator_action_under_discretization_to_continuum_operator_supplied
  boundary_trace_approximation_supplied :=
    witness.boundary_trace_approximation_supplied
  green_identity_compatibility_supplied :=
    witness.green_identity_compatibility_supplied

/-- A supplied explicit witness satisfies the convergence contract. -/
theorem approximation_convergence_witness_satisfies_contract
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    ApproximationConvergenceContractClosed witness.contract := by
  exact approximation_convergence_contract_witness_supplies_closed
    (contractWitnessOfApproximationConvergenceWitness witness)

/-- A supplied explicit witness includes finite integral/pairing evidence. -/
theorem approximation_convergence_witness_finite_integral_pairing
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.contract.finite_integral_pairing_to_continuum_pairing :=
  witness.finite_integral_pairing_to_continuum_pairing_supplied

/-- A supplied explicit witness includes reconstructed-field evidence. -/
theorem approximation_convergence_witness_reconstructed_field
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.contract.reconstructed_field_to_continuum_field :=
  witness.reconstructed_field_to_continuum_field_supplied

/-- A supplied explicit witness includes operator-action evidence. -/
theorem approximation_convergence_witness_operator_action
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.contract.operator_action_under_discretization_to_continuum_operator :=
  witness.operator_action_under_discretization_to_continuum_operator_supplied

/-- A supplied explicit witness includes boundary-trace evidence. -/
theorem approximation_convergence_witness_boundary_trace
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.contract.boundary_trace_approximation :=
  witness.boundary_trace_approximation_supplied

/-- A supplied explicit witness includes Green-identity compatibility evidence. -/
theorem approximation_convergence_witness_green_identity
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.contract.green_identity_compatibility :=
  witness.green_identity_compatibility_supplied

/-- A supplied explicit witness implies the chosen scheme's convergence meaning. -/
theorem approximation_convergence_witness_supplies_scheme_meaning
    {ContinuumPoint : Type}
    (witness : ApproximationConvergenceWitness ContinuumPoint) :
    witness.scheme.convergenceMeaning := by
  exact approximation_contract_witness_supplies_scheme_meaning
    (contractWitnessOfApproximationConvergenceWitness witness)

/-- Current repository status for the approximation-convergence witness. -/
structure ApproximationConvergenceWitnessStatus where
  convergence_witness_surface_defined : Prop
  convergence_witness_surface_defined_supplied :
    convergence_witness_surface_defined
  analytic_convergence_evidence_closed : Prop
  analytic_convergence_evidence_not_closed :
    Not analytic_convergence_evidence_closed
  retained_blocker_id : String

/-- Current status: witness shape defined, actual analytic evidence retained. -/
def approximationConvergenceWitnessStatusV0 :
    ApproximationConvergenceWitnessStatus where
  convergence_witness_surface_defined := True
  convergence_witness_surface_defined_supplied := True.intro
  analytic_convergence_evidence_closed := False
  analytic_convergence_evidence_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C3ApproximationConvergenceWitnessRetainedId

/-- The current status explicitly keeps analytic convergence evidence open. -/
theorem approximation_convergence_witness_status_v0_not_closed :
    Not approximationConvergenceWitnessStatusV0.analytic_convergence_evidence_closed := by
  exact approximationConvergenceWitnessStatusV0.analytic_convergence_evidence_not_closed

/-- This slice targets the contract link to the scheme convergence meaning. -/
theorem phase1_blocker003a1a1c3_targets_contract_meaning_link :
    phase1Blocker003A1A1C3TargetsContractObject =
      phase1Blocker003A1A1C3ExpectedContractObject := by
  rfl

/--
003A1A1C3 readout.  The witness shape is named, but actual analytic evidence
for the convergence clauses remains retained.
-/
def phase1Blocker003A1A1C3ApproximationConvergenceWitnessV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized while the convergence witness is retained. -/
theorem phase1_blocker003a1a1c3_witness_v0_phase2_not_authorized :
    Not phase1Blocker003A1A1C3ApproximationConvergenceWitnessV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumApproximationConvergenceWitness
end QFT
end ToeFormal
