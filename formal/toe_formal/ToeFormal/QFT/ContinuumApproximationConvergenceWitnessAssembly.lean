/-
ToeFormal/QFT/ContinuumApproximationConvergenceWitnessAssembly.lean

Approximation-convergence witness assembly/readout surface for
APPROXIMATION_CONVERGENCE_WITNESS_FIELDS_SPLIT_COMPLETE_BUT_RETAINED.

Scope:
- confirm that all five approximation-convergence witness evidence fields have
  been structurally split into named retained surfaces
- record that the parent approximation-convergence witness remains retained
  because no analytic evidence field has been discharged
- record that Phase 2 remains unauthorized
- do not prove convergence, Green identity discharge, continuum analytic
  closure, operator-domain closure, integration regularity, residual separation,
  or Phase 2 authorization
-/

import ToeFormal.QFT.ContinuumFiniteIntegralPairingConvergenceEvidence
import ToeFormal.QFT.ContinuumReconstructedFieldConvergenceEvidence
import ToeFormal.QFT.ContinuumOperatorActionConvergenceEvidence
import ToeFormal.QFT.ContinuumBoundaryTraceConvergenceEvidence
import ToeFormal.QFT.ContinuumGreenIdentityCompatibilityEvidence

namespace ToeFormal
namespace QFT
namespace ContinuumApproximationConvergenceWitnessAssembly

open ContinuumAnalyticBlocker003
open ContinuumApproximationConvergenceWitness
open ContinuumFiniteIntegralPairingConvergenceEvidence
open ContinuumReconstructedFieldConvergenceEvidence
open ContinuumOperatorActionConvergenceEvidence
open ContinuumBoundaryTraceConvergenceEvidence
open ContinuumGreenIdentityCompatibilityEvidence
set_option autoImplicit false

noncomputable section

/-- Machine-facing readout id for the completed field split. -/
def approximationConvergenceWitnessFieldsSplitCompleteButRetainedId : String :=
  "APPROXIMATION_CONVERGENCE_WITNESS_FIELDS_SPLIT_COMPLETE_BUT_RETAINED"

/-- Parent retained witness blocker id. -/
def phase1Blocker003A1A1C3WitnessAssemblyRetainedId : String :=
  phase1Blocker003A1A1C3ApproximationConvergenceWitnessRetainedId

/-- The five evidence fields required by an approximation-convergence witness. -/
inductive ApproximationConvergenceWitnessEvidenceField where
  | finiteIntegralPairing
  | reconstructedField
  | operatorAction
  | boundaryTrace
  | greenIdentityCompatibility
deriving DecidableEq, Repr

/-- Retained blocker ids for the five already-split evidence fields. -/
def approximationConvergenceWitnessEvidenceFieldRetainedId :
    ApproximationConvergenceWitnessEvidenceField -> String
  | .finiteIntegralPairing =>
      phase1Blocker003A1A1C3AFiniteIntegralPairingConvergenceEvidenceRetainedId
  | .reconstructedField =>
      phase1Blocker003A1A1C3BReconstructedFieldConvergenceEvidenceRetainedId
  | .operatorAction =>
      phase1Blocker003A1A1C3COperatorActionConvergenceEvidenceRetainedId
  | .boundaryTrace =>
      phase1Blocker003A1A1C3DBoundaryTraceConvergenceEvidenceRetainedId
  | .greenIdentityCompatibility =>
      phase1Blocker003A1A1C3EGreenIdentityCompatibilityEvidenceRetainedId

/-- Exact evidence-field split inventory for the parent witness. -/
def approximationConvergenceWitnessEvidenceFieldsV0 :
    List ApproximationConvergenceWitnessEvidenceField :=
  [ .finiteIntegralPairing
  , .reconstructedField
  , .operatorAction
  , .boundaryTrace
  , .greenIdentityCompatibility
  ]

/-- The witness evidence-field inventory contains exactly A-E. -/
theorem approximation_convergence_witness_fields_v0_expected :
    approximationConvergenceWitnessEvidenceFieldsV0 =
      [ .finiteIntegralPairing
      , .reconstructedField
      , .operatorAction
      , .boundaryTrace
      , .greenIdentityCompatibility
      ] := by
  rfl

/-- The retained field ids match the five split evidence blockers. -/
theorem approximation_convergence_witness_field_retained_ids_v0_expected :
    approximationConvergenceWitnessEvidenceFieldsV0.map
        approximationConvergenceWitnessEvidenceFieldRetainedId =
      [ phase1Blocker003A1A1C3AFiniteIntegralPairingConvergenceEvidenceRetainedId
      , phase1Blocker003A1A1C3BReconstructedFieldConvergenceEvidenceRetainedId
      , phase1Blocker003A1A1C3COperatorActionConvergenceEvidenceRetainedId
      , phase1Blocker003A1A1C3DBoundaryTraceConvergenceEvidenceRetainedId
      , phase1Blocker003A1A1C3EGreenIdentityCompatibilityEvidenceRetainedId
      ] := by
  rfl

/--
Assembly/readout for the approximation-convergence witness field split.

The five status objects are imported from the A-E evidence surfaces.  The
assembly status is intentionally weaker than a witness: it says the fields are
split and retained, not that the analytic evidence has been supplied.
-/
structure ApproximationConvergenceWitnessAssemblyReadout where
  finite_integral_pairing_status :
    FiniteIntegralPairingConvergenceEvidenceStatus
  reconstructed_field_status :
    ReconstructedFieldConvergenceEvidenceStatus
  operator_action_status :
    OperatorActionConvergenceEvidenceStatus
  boundary_trace_status :
    BoundaryTraceConvergenceEvidenceStatus
  green_identity_compatibility_status :
    GreenIdentityCompatibilityEvidenceStatus
  all_five_witness_fields_structurally_split : Prop
  all_five_witness_fields_structurally_split_supplied :
    all_five_witness_fields_structurally_split
  analytic_convergence_witness_closed : Prop
  analytic_convergence_witness_not_closed :
    Not analytic_convergence_witness_closed
  retained_parent_witness_blocker_id : String
  readout_id : String
  phase2_authorized : Prop
  phase2_not_authorized : Not phase2_authorized

/--
Current readout: the five evidence fields are structurally split, but the
parent approximation-convergence witness remains retained.
-/
def approximationConvergenceWitnessAssemblyReadoutV0 :
    ApproximationConvergenceWitnessAssemblyReadout where
  finite_integral_pairing_status :=
    finiteIntegralPairingConvergenceEvidenceStatusV0
  reconstructed_field_status :=
    reconstructedFieldConvergenceEvidenceStatusV0
  operator_action_status :=
    operatorActionConvergenceEvidenceStatusV0
  boundary_trace_status :=
    boundaryTraceConvergenceEvidenceStatusV0
  green_identity_compatibility_status :=
    greenIdentityCompatibilityEvidenceStatusV0
  all_five_witness_fields_structurally_split := True
  all_five_witness_fields_structurally_split_supplied := True.intro
  analytic_convergence_witness_closed := False
  analytic_convergence_witness_not_closed := by
    intro h
    exact h
  retained_parent_witness_blocker_id :=
    phase1Blocker003A1A1C3WitnessAssemblyRetainedId
  readout_id :=
    approximationConvergenceWitnessFieldsSplitCompleteButRetainedId
  phase2_authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short alias for local readout theorems. -/
def assemblyReadoutV0 : ApproximationConvergenceWitnessAssemblyReadout :=
  approximationConvergenceWitnessAssemblyReadoutV0

/-- The assembly readout confirms that all five witness fields have been split. -/
theorem approximation_convergence_witness_fields_split_complete_v0 :
    assemblyReadoutV0.all_five_witness_fields_structurally_split := by
  exact assemblyReadoutV0.all_five_witness_fields_structurally_split_supplied

/--
Despite the completed field split, the parent convergence witness remains
analytically retained.
-/
theorem approximation_convergence_witness_fields_split_but_retained_v0 :
    Not assemblyReadoutV0.analytic_convergence_witness_closed := by
  exact assemblyReadoutV0.analytic_convergence_witness_not_closed

/-- The assembly readout exposes the expected machine-facing readout id. -/
theorem approximation_convergence_witness_assembly_readout_id_v0 :
    assemblyReadoutV0.readout_id =
      approximationConvergenceWitnessFieldsSplitCompleteButRetainedId := by
  rfl

/-- The assembly readout keeps the parent approximation witness blocker retained. -/
theorem approximation_convergence_witness_parent_blocker_still_retained :
    assemblyReadoutV0.retained_parent_witness_blocker_id =
      phase1Blocker003A1A1C3ApproximationConvergenceWitnessRetainedId := by
  rfl

/--
003A1A1C3 assembly readout.  The approximation witness field split is complete
as inventory, but all analytic closure obligations remain retained.
-/
def phase1Blocker003A1A1C3WitnessAssemblyReadoutV0 :
    Phase1Blocker003Split where
  boundaryTermVanishingStatus := .retained
  operatorDomainClosureStatus := .retained
  residualSeparationStatus := .retained
  smoothnessAdmissibleVariationStatus := .retained
  integrationLinearityStatus := .retained
  phase2Authorized := False

/-- Phase 2 remains unauthorized after the witness-field assembly readout. -/
theorem phase1_blocker003a1a1c3_witness_assembly_v0_phase2_not_authorized :
    Not phase1Blocker003A1A1C3WitnessAssemblyReadoutV0.phase2Authorized := by
  intro h
  exact h

/-- The assembly-specific readout also records that Phase 2 is unauthorized. -/
theorem approximation_convergence_witness_assembly_readout_v0_phase2_not_authorized :
    Not assemblyReadoutV0.phase2_authorized := by
  exact assemblyReadoutV0.phase2_not_authorized

end
end ContinuumApproximationConvergenceWitnessAssembly
end QFT
end ToeFormal
