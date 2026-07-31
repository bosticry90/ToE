import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0
import ToeFormal.Release.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationResultReviewV0

/-
Release-facing current-authority aggregate for tiered validation. It is a small
build target for authority-surface synchronization checks and intentionally
does not replace the full ToeFormal release aggregate.
-/

namespace ToeFormal
namespace Release
namespace CurrentAuthority

open Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyBoundedProgramPreparationResultReview

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

theorem current_authority_tracks_prepared_gravitational_survey_program_proposal :
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

theorem gravitational_survey_program_is_installed_and_remains_unopened :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY" ∧
    boundedAttemptNumber = 0 ∧
    proposalPrepared = true ∧
    independentReviewAccepted = true ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0.programInstalled =
      true ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationV0.programOpened =
      false ∧
    ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyProgramGovernanceInstallationResultReviewV0.installationAccepted =
      true ∧
    scientificStageOpened = false ∧
    compatibilitySurveyExecuted = false ∧
    gravitationalActionSelected = false ∧
    evidencePromoted = false ∧
    automaticSuccessorSelected = false ∧
    closedV2MatrixPopulationPermitted = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
