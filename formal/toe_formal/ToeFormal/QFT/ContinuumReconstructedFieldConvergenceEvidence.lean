/-
ToeFormal/QFT/ContinuumReconstructedFieldConvergenceEvidence.lean

Reconstructed-field convergence evidence surface for
PHASE1-BLOCKER-003A1A1C3B_RECONSTRUCTED_FIELD_CONVERGENCE_EVIDENCE_RETAINED.

Scope:
- split the reconstructed-field approximation-convergence witness evidence field
- record the continuum field target and finite reconstruction relation shape
- state the reconstructed-field convergence proposition
- connect supplied evidence to the approximation-convergence witness field
- prove only conditional wiring lemmas
- do not prove analytic reconstructed-field convergence
- do not claim Green identity discharge, operator-domain closure, integration
  regularity, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumApproximationConvergenceWitness

namespace ToeFormal
namespace QFT
namespace ContinuumReconstructedFieldConvergenceEvidence

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumApproximationConvergenceContract
open ContinuumApproximationConvergenceWitness
set_option autoImplicit false

noncomputable section

/-- Retained id for reconstructed-field convergence evidence. -/
def phase1Blocker003A1A1C3BReconstructedFieldConvergenceEvidenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3B_RECONSTRUCTED_FIELD_CONVERGENCE_EVIDENCE_RETAINED"

/-- The witness object targeted by this evidence slice. -/
def phase1Blocker003A1A1C3BTargetsWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .reconstructedFieldEvidence

/-- Expected witness object for this evidence slice. -/
def phase1Blocker003A1A1C3BExpectedWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .reconstructedFieldEvidence

/-- Missing objects for actual reconstructed-field convergence evidence. -/
inductive Phase1Blocker003A1A1C3BReconstructedFieldMissingObject where
  | continuumFieldTarget
  | finiteApproximationMapFamily
  | reconstructionMapFamily
  | reconstructedFieldLimitStatement
  | contractFieldLink
  | analyticConvergenceEvidence
deriving DecidableEq, Repr

/-- Machine-facing ids for retained reconstructed-field evidence objects. -/
def phase1Blocker003A1A1C3BReconstructedFieldMissingObjectId :
    Phase1Blocker003A1A1C3BReconstructedFieldMissingObject -> String
  | .continuumFieldTarget =>
      "003A1A1C3B_CONTINUUM_FIELD_TARGET_RETAINED"
  | .finiteApproximationMapFamily =>
      "003A1A1C3B_FINITE_APPROXIMATION_MAP_FAMILY_RETAINED"
  | .reconstructionMapFamily =>
      "003A1A1C3B_RECONSTRUCTION_MAP_FAMILY_RETAINED"
  | .reconstructedFieldLimitStatement =>
      "003A1A1C3B_RECONSTRUCTED_FIELD_LIMIT_STATEMENT_RETAINED"
  | .contractFieldLink =>
      "003A1A1C3B_CONTRACT_FIELD_LINK_RETAINED"
  | .analyticConvergenceEvidence =>
      "003A1A1C3B_ANALYTIC_CONVERGENCE_EVIDENCE_RETAINED"

/-- Exact retained objects for reconstructed-field convergence evidence. -/
def phase1Blocker003A1A1C3BReconstructedFieldMissingObjectsV0 :
    List Phase1Blocker003A1A1C3BReconstructedFieldMissingObject :=
  [ .continuumFieldTarget
  , .finiteApproximationMapFamily
  , .reconstructionMapFamily
  , .reconstructedFieldLimitStatement
  , .contractFieldLink
  , .analyticConvergenceEvidence
  ]

/-- The retained-object list for this evidence field is explicit. -/
theorem phase1_blocker003a1a1c3b_missing_objects_v0_expected :
    phase1Blocker003A1A1C3BReconstructedFieldMissingObjectsV0 =
      [ .continuumFieldTarget
      , .finiteApproximationMapFamily
      , .reconstructionMapFamily
      , .reconstructedFieldLimitStatement
      , .contractFieldLink
      , .analyticConvergenceEvidence
      ] := by
  rfl

/--
The reconstructed continuum field induced by sampling a continuum field onto a
finite refinement and applying the scheme reconstruction map.
-/
def reconstructedFieldOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) :
    ContinuumField ContinuumPoint :=
  scheme.reconstructionMap r (scheme.approximationMap r field)

/-- The scheme-level reconstructed field is definitionally reconstruction after sampling. -/
theorem reconstructed_field_of_scheme_eq_reconstruction_after_approximation
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) :
    reconstructedFieldOfScheme scheme r field =
      scheme.reconstructionMap r (scheme.approximationMap r field) := by
  rfl

/--
Focused evidence object for the reconstructed-field convergence field.

The convergence statement is intentionally a proposition supplied by the caller.
This surface records the continuum field target, the finite reconstruction shape,
and the link from that statement into the contract field.
-/
structure ReconstructedFieldConvergenceEvidence
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (contract : ApproximationConvergenceContract scheme) where
  continuumFieldTarget : ContinuumField ContinuumPoint
  reconstructed_field_convergence_statement : Prop
  reconstructed_field_convergence_statement_supplied :
    reconstructed_field_convergence_statement
  statement_supplies_contract_field :
    reconstructed_field_convergence_statement ->
      contract.reconstructed_field_to_continuum_field

/-- Supplied reconstructed-field evidence fills the contract field. -/
theorem reconstructed_field_evidence_supplies_contract_field
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      ReconstructedFieldConvergenceEvidence scheme contract) :
    contract.reconstructed_field_to_continuum_field :=
  evidence.statement_supplies_contract_field
    evidence.reconstructed_field_convergence_statement_supplied

/--
Build the full approximation-convergence witness when this reconstructed-field
evidence and the remaining four evidence fields are supplied.
-/
def approximationConvergenceWitnessOfReconstructedFieldEvidence
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      ReconstructedFieldConvergenceEvidence scheme contract)
    (finiteIntegralPairing :
      contract.finite_integral_pairing_to_continuum_pairing)
    (operatorAction :
      contract.operator_action_under_discretization_to_continuum_operator)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceWitness ContinuumPoint where
  scheme := scheme
  contract := contract
  finite_integral_pairing_to_continuum_pairing_supplied :=
    finiteIntegralPairing
  reconstructed_field_to_continuum_field_supplied :=
    reconstructed_field_evidence_supplies_contract_field evidence
  operator_action_under_discretization_to_continuum_operator_supplied :=
    operatorAction
  boundary_trace_approximation_supplied := boundaryTrace
  green_identity_compatibility_supplied := greenIdentity

/-- The witness built from reconstructed-field evidence satisfies the contract. -/
theorem reconstructed_field_evidence_builds_contract_witness
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      ReconstructedFieldConvergenceEvidence scheme contract)
    (finiteIntegralPairing :
      contract.finite_integral_pairing_to_continuum_pairing)
    (operatorAction :
      contract.operator_action_under_discretization_to_continuum_operator)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceContractClosed contract := by
  exact approximation_convergence_witness_satisfies_contract
    (approximationConvergenceWitnessOfReconstructedFieldEvidence
      evidence finiteIntegralPairing operatorAction boundaryTrace greenIdentity)

/-- Current repository status for reconstructed-field convergence evidence. -/
structure ReconstructedFieldConvergenceEvidenceStatus where
  evidence_surface_defined : Prop
  evidence_surface_defined_supplied : evidence_surface_defined
  analytic_reconstructed_field_convergence_closed : Prop
  analytic_reconstructed_field_convergence_not_closed :
    Not analytic_reconstructed_field_convergence_closed
  retained_blocker_id : String

/-- Current status: evidence shape defined, analytic convergence retained. -/
def reconstructedFieldConvergenceEvidenceStatusV0 :
    ReconstructedFieldConvergenceEvidenceStatus where
  evidence_surface_defined := True
  evidence_surface_defined_supplied := True.intro
  analytic_reconstructed_field_convergence_closed := False
  analytic_reconstructed_field_convergence_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C3BReconstructedFieldConvergenceEvidenceRetainedId

/-- Short local status alias used by the readout theorem. -/
def evidenceStatusV0 : ReconstructedFieldConvergenceEvidenceStatus :=
  reconstructedFieldConvergenceEvidenceStatusV0

/-- The current status keeps reconstructed-field convergence open. -/
theorem reconstructed_field_convergence_status_v0_not_closed :
    Not evidenceStatusV0.analytic_reconstructed_field_convergence_closed := by
  exact evidenceStatusV0.analytic_reconstructed_field_convergence_not_closed

/-- This slice targets the reconstructed-field evidence field. -/
theorem phase1_blocker003a1a1c3b_targets_witness_field :
    phase1Blocker003A1A1C3BTargetsWitnessObject =
      phase1Blocker003A1A1C3BExpectedWitnessObject := by
  rfl

/--
003A1A1C3B readout.  The evidence field is named, but actual analytic
reconstructed-field convergence remains retained.
-/
def phase1Blocker003A1A1C3BReconstructedFieldEvidenceV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Short local phase readout alias used by the Phase 2 theorem. -/
def evidencePhaseReadoutV0 : Phase1Blocker003Split :=
  phase1Blocker003A1A1C3BReconstructedFieldEvidenceV0

/-- Phase 2 remains unauthorized while this evidence field is retained. -/
theorem phase1_blocker003a1a1c3b_evidence_v0_phase2_not_authorized :
    Not evidencePhaseReadoutV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumReconstructedFieldConvergenceEvidence
end QFT
end ToeFormal
