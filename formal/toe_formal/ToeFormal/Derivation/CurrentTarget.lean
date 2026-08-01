import ToeFormal.Derivation.ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview
import ToeFormal.Release.ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_PROGRAM_GOVERNANCE_INSTALLATION_v0"
def currentBoundedProgramId : String := proposedProgramId
def currentBoundedProgramState : String := "UNOPENED"
def currentTargetPhase : String :=
  "TARGETED_CCFT_RECOVERY_PROGRAM_INSTALLED_UNOPENED"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "MINIMAL_CLOSED_CCFT_CORE_DECISION"
def lastBoundedTerminalResult : String := "BLOCKED"

theorem current_target_records_installed_targeted_recovery_program :
    currentLiveTarget =
      "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0" := by
  rfl

theorem targeted_recovery_program_is_installed_but_unopened :
    currentBoundedProgramId = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0" ∧
    currentBoundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "TARGETED_CCFT_RECOVERY_PROGRAM_INSTALLED_UNOPENED" ∧
    currentBoundedAttemptNumber = 0 ∧ proposedStageCount = 4 ∧
    searchPassLimit = 1 ∧ repairAttemptCount = 0 ∧
    Release.ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.programInstalled =
      true ∧
    Release.ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.programOpened =
      false ∧
    Release.ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.archiveTraversalExecuted =
      false ∧
    scientificStageOpened = false ∧ archiveSearchExecuted = false ∧
    contractRecovered = false ∧ ccftEquationRepairedOrSelected = false ∧
    newCCFTPostulateInserted = false ∧ ccftV0Constructed = false ∧
    constructionPreparationAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
