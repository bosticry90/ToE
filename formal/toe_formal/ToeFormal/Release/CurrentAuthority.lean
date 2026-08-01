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

theorem current_authority_tracks_prepared_targeted_recovery_program_proposal :
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

theorem targeted_recovery_program_proposal_is_prepared_but_uninstalled :
    boundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    boundedProgramState = "PROPOSAL_PREPARED_UNINSTALLED" ∧
    currentTargetPhase =
      "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY" ∧
    boundedAttemptNumber = 0 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.proposedStageCount = 4 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.searchPassLimit = 1 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.repairAttemptCount = 0 ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.programInstalled = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.scientificStageOpened = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.archiveSearchExecuted = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.contractRecovered = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.constructionPreparationAuthorized = false ∧
    Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview.automaticSecondSearch = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
