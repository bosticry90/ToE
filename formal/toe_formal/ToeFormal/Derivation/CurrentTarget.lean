import ToeFormal.Derivation.ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationResultReview
import ToeFormal.Release.ToeCCFTCoreProgramGovernanceInstallationV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationResultReview

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String :=
  "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_PROGRAM_GOVERNANCE_INSTALLATION_v0"
def currentBoundedProgramId : String := proposedProgramId
def currentBoundedProgramState : String := "UNOPENED"
def currentTargetPhase : String :=
  "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY"
def currentBoundedAttemptNumber : Nat := 0
def lastClosedBoundedSemanticStage : String := "NONE"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_installed_ccft_core_program :
    currentLiveTarget = executionTarget := by
  rfl

theorem ccft_core_program_is_installed_but_unopened :
    currentBoundedProgramState = "UNOPENED" ∧
    currentTargetPhase =
      "PROGRAM_INSTALLED_AWAITING_SEPARATE_STAGE_1_AUTHORITY" ∧
    currentBoundedAttemptNumber = 0 ∧
    proposedStageCount = 5 ∧ repairAttemptCount = 0 ∧
    Release.ToeCCFTCoreProgramGovernanceInstallationV0.programInstalled = true ∧
    Release.ToeCCFTCoreProgramGovernanceInstallationV0.programOpened = false ∧
    scientificStageOpened = false ∧
    ccftMathematicalCoreRecovered = false ∧
    operationalCoherenceDefinitionEstablished = false ∧
    ccftRepresentationFieldOrActionSelected = false ∧
    ccftSeamObservableOrDiscriminatorSelected = false ∧
    evidencePromoted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
