import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"

def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat := Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_selected_mandatory_exit :
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

theorem eligibility_handoff_closed_with_nonexecuting_route_only :
    boundedProgramId =
      "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase = "MANDATORY_EXIT_SELECTED_NOT_EXECUTED" ∧
    boundedAttemptNumber = 5 ∧
    Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult.eligibleNativeActionFamilyCount = 0 ∧
    Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult.selectedRoute =
      "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE" ∧
    Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult.gravitationalActionsSelected = 0 ∧
    Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult.nativeGravitationalPrinciplesSelectedOrDerived = 0 ∧
    Derivation.ToeGravitationalActionFamilyEligibilityHandoffResult.successorProgramsAuthorizedInstalledOrOpened = 0 := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
