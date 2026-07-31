import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

/-
Release-facing current-authority aggregate for tiered validation. It is a small
build target for authority-surface synchronization checks and intentionally
does not replace the full ToeFormal release aggregate.
-/

namespace ToeFormal
namespace Release
namespace CurrentAuthority

open Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyPreparationAuthorityV0

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String :=
  Derivation.CurrentTarget.currentLiveTarget

def currentEvidencePacketId : String :=
  Derivation.CurrentTarget.currentEvidencePacketId

def boundedProgramId : String :=
  Derivation.CurrentTarget.currentBoundedProgramId

def boundedProgramState : String :=
  Derivation.CurrentTarget.currentBoundedProgramState

def currentTargetPhase : String :=
  Derivation.CurrentTarget.currentTargetPhase

def boundedAttemptNumber : Nat :=
  Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_gravitational_survey_proposal_preparation :
    currentTarget =
      "prepare_toe_native_gravitational_requirements_and_candidate_action_family_survey_bounded_program_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated =
      false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem gravitational_survey_preparation_has_no_scientific_execution_authority :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "UNINSTALLED" ∧
    currentTargetPhase =
      "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED" ∧
    boundedAttemptNumber = 0 ∧
    proposalPreparationAuthorized = true ∧
    programInstalled = false ∧
    scientificStageOpened = false ∧
    compatibilityCellsAdjudicated = false ∧
    gravitationalActionSelected = false ∧
    evidencePromoted = false ∧
    scientificSuccessorAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
