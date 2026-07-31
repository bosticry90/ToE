import ToeFormal.Derivation.ToeCCFTSourceBoundMathematicalInventoryAttemptOpen
import ToeFormal.Release.ToeCCFTCoreProgramGovernanceInstallationV0
import ToeFormal.Release.ToeCCFTCoreProgramGovernanceInstallationResultReviewV0

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTSourceBoundMathematicalInventoryAttemptOpen

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := scientificTarget
def currentEvidencePacketId : String := eventId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "OPEN"
def currentTargetPhase : String := "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN"
def currentBoundedAttemptNumber : Nat := 1
def lastClosedBoundedSemanticStage : String := "NONE_IN_CURRENT_PROGRAM"
def lastBoundedTerminalResult : String := "NONE"

theorem current_target_records_open_ccft_mathematical_inventory :
    currentLiveTarget =
      "inventory_toe_source_bound_ccft_mathematical_structures_v0" := by
  rfl

theorem ccft_mathematical_inventory_is_open_without_result :
    currentBoundedProgramState = "OPEN" ∧
    currentTargetPhase = "STAGE_1_SCIENTIFIC_ATTEMPT_OPEN" ∧
    currentBoundedAttemptNumber = 1 ∧
    lastClosedBoundedSemanticStage = "NONE_IN_CURRENT_PROGRAM" ∧
    lastBoundedTerminalResult = "NONE" ∧
    Release.ToeCCFTCoreProgramGovernanceInstallationV0.programInstalled = true ∧
    Release.ToeCCFTCoreProgramGovernanceInstallationV0.programOpened = false ∧
    Release.ToeCCFTCoreProgramGovernanceInstallationResultReviewV0.installationAccepted =
      true ∧
    programOpen = true ∧ scientificResultCreated = false ∧
    deepReviewSourcesSelected = 0 ∧ ccftMathematicalInventoryEntries = 0 ∧
    operationalInterpretationEstablished = false ∧
    minimalCCFTCoreSelected = false ∧
    representationFieldActionSeamOrObservableSelected = false ∧
    ccftModelOrPhysicalClaimEstablished = false ∧ evidencePromoted = false ∧
    stageTwoAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
