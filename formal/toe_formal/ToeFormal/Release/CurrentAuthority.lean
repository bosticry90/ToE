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

theorem current_authority_tracks_terminal_ccft_core_program_exit :
    currentTarget =
      "close_toe_ccft_native_mathematical_core_and_operationalization_v0_after_bounded_result_v0" := by
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

theorem ccft_core_program_is_terminal_after_stage_four_block :
    boundedProgramId =
      "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0" ∧
    boundedProgramState = "CLOSED" ∧
    currentTargetPhase = "PROGRAM_CLOSED_AFTER_MANDATORY_EXIT" ∧
    boundedAttemptNumber = 4 ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.terminalOutcome =
      "NO_CLOSED_CCFT_MATHEMATICAL_CORE_RECOVERED" ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.mandatoryExitCompleted = true ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.stageFourBlocked = true ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.stageFiveAttempted = false ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.closedSourceBoundSurrogateCoreRecovered = false ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.newCCFTPostulateInserted = false ∧
    Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationV0BoundedCloseout.successorProgramAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
