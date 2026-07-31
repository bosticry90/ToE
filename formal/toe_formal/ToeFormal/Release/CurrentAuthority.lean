import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

open Derivation.ToeNativeGravitationalRequirementsAndCandidateActionFamilySurveyV0BoundedCloseout

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat := Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_completed_gravitational_survey_mandatory_exit :
    currentTarget =
      "close_toe_native_gravitational_requirements_and_candidate_action_family_survey_v0_after_bounded_result_v0" := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated = false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem gravitational_survey_mandatory_exit_is_terminal :
    boundedProgramState = "TERMINAL" ∧
    currentTargetPhase = "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT" ∧
    boundedAttemptNumber = 5 ∧ mandatoryExitCompleted = true ∧
    eligibleNativeActionFamilyCount = 0 ∧
    positiveNativeGravitationalPrincipleSelectedOrDerived = false ∧
    nativeGravitationalActionSelectedOrAdopted = false ∧
    successorProgramAuthorized = false ∧ successorProgramInstalled = false ∧
    successorProgramOpened = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
