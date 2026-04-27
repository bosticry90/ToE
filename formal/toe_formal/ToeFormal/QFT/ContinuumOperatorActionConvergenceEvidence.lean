/-
ToeFormal/QFT/ContinuumOperatorActionConvergenceEvidence.lean

Operator-action convergence evidence surface for
PHASE1-BLOCKER-003A1A1C3C_OPERATOR_ACTION_CONVERGENCE_EVIDENCE_RETAINED.

Scope:
- split the operator-action approximation-convergence witness evidence field
- record the finite/discrete operator family and continuum scalar kinetic
  operator target
- state the operator-action convergence proposition
- connect supplied evidence to the approximation-convergence witness field
- prove only conditional wiring lemmas
- do not prove analytic operator-action convergence
- do not claim Green identity discharge, operator-domain closure, integration
  regularity, residual separation, or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumApproximationConvergenceWitness

namespace ToeFormal
namespace QFT
namespace ContinuumOperatorActionConvergenceEvidence

open ContinuumAnalyticBlocker003
open ContinuumFirstVariation
open ContinuumFiniteApproximationScheme
open ContinuumApproximationConvergenceContract
open ContinuumApproximationConvergenceWitness
set_option autoImplicit false

noncomputable section

/-- Retained id for operator-action convergence evidence. -/
def phase1Blocker003A1A1C3COperatorActionConvergenceEvidenceRetainedId :
    String :=
  "PHASE1-BLOCKER-003A1A1C3C_OPERATOR_ACTION_CONVERGENCE_EVIDENCE_RETAINED"

/-- The witness object targeted by this evidence slice. -/
def phase1Blocker003A1A1C3CTargetsWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .operatorActionEvidence

/-- Expected witness object for this evidence slice. -/
def phase1Blocker003A1A1C3CExpectedWitnessObject :
    Phase1Blocker003A1A1C3ApproximationConvergenceWitnessMissingObject :=
  .operatorActionEvidence

/-- Missing objects for actual operator-action convergence evidence. -/
inductive Phase1Blocker003A1A1C3COperatorActionMissingObject where
  | finiteOperatorFamily
  | continuumScalarKineticOperator
  | sampledFieldOperatorAction
  | reconstructedOperatorActionStatement
  | contractFieldLink
  | analyticConvergenceEvidence
deriving DecidableEq, Repr

/-- Machine-facing ids for retained operator-action evidence objects. -/
def phase1Blocker003A1A1C3COperatorActionMissingObjectId :
    Phase1Blocker003A1A1C3COperatorActionMissingObject -> String
  | .finiteOperatorFamily =>
      "003A1A1C3C_FINITE_OPERATOR_FAMILY_RETAINED"
  | .continuumScalarKineticOperator =>
      "003A1A1C3C_CONTINUUM_SCALAR_KINETIC_OPERATOR_RETAINED"
  | .sampledFieldOperatorAction =>
      "003A1A1C3C_SAMPLED_FIELD_OPERATOR_ACTION_RETAINED"
  | .reconstructedOperatorActionStatement =>
      "003A1A1C3C_RECONSTRUCTED_OPERATOR_ACTION_STATEMENT_RETAINED"
  | .contractFieldLink =>
      "003A1A1C3C_CONTRACT_FIELD_LINK_RETAINED"
  | .analyticConvergenceEvidence =>
      "003A1A1C3C_ANALYTIC_CONVERGENCE_EVIDENCE_RETAINED"

/-- Exact retained objects for operator-action convergence evidence. -/
def phase1Blocker003A1A1C3COperatorActionMissingObjectsV0 :
    List Phase1Blocker003A1A1C3COperatorActionMissingObject :=
  [ .finiteOperatorFamily
  , .continuumScalarKineticOperator
  , .sampledFieldOperatorAction
  , .reconstructedOperatorActionStatement
  , .contractFieldLink
  , .analyticConvergenceEvidence
  ]

/-- The retained-object list for this evidence field is explicit. -/
theorem phase1_blocker003a1a1c3c_missing_objects_v0_expected :
    phase1Blocker003A1A1C3COperatorActionMissingObjectsV0 =
      [ .finiteOperatorFamily
      , .continuumScalarKineticOperator
      , .sampledFieldOperatorAction
      , .reconstructedOperatorActionStatement
      , .contractFieldLink
      , .analyticConvergenceEvidence
      ] := by
  rfl

/-- Finite operator action induced by a scheme-level finite operator family. -/
def finiteOperatorActionOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteOperator :
      (r : scheme.RefinementParameter) ->
        ContinuumField (scheme.FiniteDomain r) ->
          ContinuumField (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter)
    (field : ContinuumField (scheme.FiniteDomain r)) :
    ContinuumField (scheme.FiniteDomain r) :=
  finiteOperator r field

/--
The continuum field obtained by sampling a continuum field, applying the finite
operator, and reconstructing the result.
-/
def reconstructedFiniteOperatorActionOfScheme
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteOperator :
      (r : scheme.RefinementParameter) ->
        ContinuumField (scheme.FiniteDomain r) ->
          ContinuumField (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) :
    ContinuumField ContinuumPoint :=
  scheme.reconstructionMap r
    (finiteOperatorActionOfScheme scheme finiteOperator r
      (scheme.approximationMap r field))

/-- Continuum operator action for the selected scalar kinetic operator. -/
def continuumOperatorAction
    {ContinuumPoint : Type}
    (continuumOperator :
      ContinuumField ContinuumPoint -> ContinuumField ContinuumPoint)
    (field : ContinuumField ContinuumPoint) :
    ContinuumField ContinuumPoint :=
  continuumOperator field

/-- The reconstructed finite action is definitionally finite action then reconstruction. -/
theorem reconstructed_finite_operator_action_eq_reconstruction_after_finite_action
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (finiteOperator :
      (r : scheme.RefinementParameter) ->
        ContinuumField (scheme.FiniteDomain r) ->
          ContinuumField (scheme.FiniteDomain r))
    (r : scheme.RefinementParameter)
    (field : ContinuumField ContinuumPoint) :
    reconstructedFiniteOperatorActionOfScheme scheme finiteOperator r field =
      scheme.reconstructionMap r
        (finiteOperator r (scheme.approximationMap r field)) := by
  rfl

/-- The continuum operator action helper exposes the selected operator. -/
theorem continuum_operator_action_eq_operator
    {ContinuumPoint : Type}
    (continuumOperator :
      ContinuumField ContinuumPoint -> ContinuumField ContinuumPoint)
    (field : ContinuumField ContinuumPoint) :
    continuumOperatorAction continuumOperator field = continuumOperator field := by
  rfl

/--
Focused evidence object for the operator-action convergence field.

The convergence statement is intentionally a proposition supplied by the caller.
This surface records the finite operator family, the continuum scalar kinetic
operator target, and the link from that statement into the contract field.
-/
structure OperatorActionConvergenceEvidence
    {ContinuumPoint : Type}
    (scheme : FiniteApproximationScheme ContinuumPoint)
    (contract : ApproximationConvergenceContract scheme) where
  finiteOperator :
    (r : scheme.RefinementParameter) ->
      ContinuumField (scheme.FiniteDomain r) ->
        ContinuumField (scheme.FiniteDomain r)
  continuumOperator :
    ContinuumField ContinuumPoint -> ContinuumField ContinuumPoint
  continuumFieldTarget : ContinuumField ContinuumPoint
  operator_action_convergence_statement : Prop
  operator_action_convergence_statement_supplied :
    operator_action_convergence_statement
  statement_supplies_contract_field :
    operator_action_convergence_statement ->
      contract.operator_action_under_discretization_to_continuum_operator

/-- Supplied operator-action evidence fills the contract field. -/
theorem operator_action_evidence_supplies_contract_field
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      OperatorActionConvergenceEvidence scheme contract) :
    contract.operator_action_under_discretization_to_continuum_operator :=
  evidence.statement_supplies_contract_field
    evidence.operator_action_convergence_statement_supplied

/--
Build the full approximation-convergence witness when this operator-action
evidence and the remaining four evidence fields are supplied.
-/
def approximationConvergenceWitnessOfOperatorActionEvidence
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      OperatorActionConvergenceEvidence scheme contract)
    (finiteIntegralPairing :
      contract.finite_integral_pairing_to_continuum_pairing)
    (reconstructed :
      contract.reconstructed_field_to_continuum_field)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceWitness ContinuumPoint where
  scheme := scheme
  contract := contract
  finite_integral_pairing_to_continuum_pairing_supplied :=
    finiteIntegralPairing
  reconstructed_field_to_continuum_field_supplied := reconstructed
  operator_action_under_discretization_to_continuum_operator_supplied :=
    operator_action_evidence_supplies_contract_field evidence
  boundary_trace_approximation_supplied := boundaryTrace
  green_identity_compatibility_supplied := greenIdentity

/-- The witness built from operator-action evidence satisfies the contract. -/
theorem operator_action_evidence_builds_contract_witness
    {ContinuumPoint : Type}
    {scheme : FiniteApproximationScheme ContinuumPoint}
    {contract : ApproximationConvergenceContract scheme}
    (evidence :
      OperatorActionConvergenceEvidence scheme contract)
    (finiteIntegralPairing :
      contract.finite_integral_pairing_to_continuum_pairing)
    (reconstructed :
      contract.reconstructed_field_to_continuum_field)
    (boundaryTrace : contract.boundary_trace_approximation)
    (greenIdentity : contract.green_identity_compatibility) :
    ApproximationConvergenceContractClosed contract := by
  exact approximation_convergence_witness_satisfies_contract
    (approximationConvergenceWitnessOfOperatorActionEvidence
      evidence finiteIntegralPairing reconstructed boundaryTrace greenIdentity)

/-- Current repository status for operator-action convergence evidence. -/
structure OperatorActionConvergenceEvidenceStatus where
  evidence_surface_defined : Prop
  evidence_surface_defined_supplied : evidence_surface_defined
  analytic_operator_action_convergence_closed : Prop
  analytic_operator_action_convergence_not_closed :
    Not analytic_operator_action_convergence_closed
  retained_blocker_id : String

/-- Current status: evidence shape defined, analytic convergence retained. -/
def operatorActionConvergenceEvidenceStatusV0 :
    OperatorActionConvergenceEvidenceStatus where
  evidence_surface_defined := True
  evidence_surface_defined_supplied := True.intro
  analytic_operator_action_convergence_closed := False
  analytic_operator_action_convergence_not_closed := by
    intro h
    exact h
  retained_blocker_id :=
    phase1Blocker003A1A1C3COperatorActionConvergenceEvidenceRetainedId

/-- Short local status alias used by the readout theorem. -/
def evidenceStatusV0 : OperatorActionConvergenceEvidenceStatus :=
  operatorActionConvergenceEvidenceStatusV0

/-- The current status keeps operator-action convergence open. -/
theorem operator_action_convergence_status_v0_not_closed :
    Not evidenceStatusV0.analytic_operator_action_convergence_closed := by
  exact evidenceStatusV0.analytic_operator_action_convergence_not_closed

/-- This slice targets the operator-action evidence field. -/
theorem phase1_blocker003a1a1c3c_targets_witness_field :
    phase1Blocker003A1A1C3CTargetsWitnessObject =
      phase1Blocker003A1A1C3CExpectedWitnessObject := by
  rfl

/--
003A1A1C3C readout.  The evidence field is named, but actual analytic
operator-action convergence remains retained.
-/
def phase1Blocker003A1A1C3COperatorActionEvidenceV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Short local phase readout alias used by the Phase 2 theorem. -/
def evidencePhaseReadoutV0 : Phase1Blocker003Split :=
  phase1Blocker003A1A1C3COperatorActionEvidenceV0

/-- Phase 2 remains unauthorized while this evidence field is retained. -/
theorem phase1_blocker003a1a1c3c_evidence_v0_phase2_not_authorized :
    Not evidencePhaseReadoutV0.phase2Authorized := by
  intro h
  exact h

end
end ContinuumOperatorActionConvergenceEvidence
end QFT
end ToeFormal
