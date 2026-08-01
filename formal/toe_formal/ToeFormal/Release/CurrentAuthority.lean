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

theorem current_authority_tracks_post_ccft_recovery_route_selection :
    currentTarget = "select_post_ccft_core_recovery_development_route_v0" := by
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

theorem post_ccft_recovery_route_selection_is_authorized_without_execution :
    boundedProgramId = "NONE" ∧ boundedProgramState = "NOT_APPLICABLE" ∧
    currentTargetPhase =
      "POST_CCFT_CORE_RECOVERY_ROUTE_SELECTION_AUTHORIZED_NOT_EXECUTED" ∧
    boundedAttemptNumber = 0 ∧
    Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority.candidateRouteCount = 3 ∧
    Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority.archiveTraversalAuthorized = false ∧
    Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority.ccftV0ProgramPreparationAuthorized = false ∧
    Derivation.ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority.newCCFTPostulateAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
