import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0

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

theorem current_authority_tracks_installed_targeted_recovery_program :
    currentTarget =
      "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0" := by
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

theorem targeted_recovery_program_is_installed_and_remains_unopened :
    boundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    boundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "TARGETED_CCFT_RECOVERY_PROGRAM_INSTALLED_UNOPENED" ∧
    boundedAttemptNumber = 0 ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.authorizedStageCount = 4 ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.targetedContentSearchPassLimit = 1 ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.repairAttemptCount = 0 ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.programInstalled = true ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.programOpened = false ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.scientificOutputCreated = false ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.archiveTraversalExecuted = false ∧
    ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.closureContractRecoveredOrRejected = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
