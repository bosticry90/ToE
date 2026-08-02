import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ModelContractFreezeStage2OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_stage_two_freeze_without_stage_three_authority :
    ToeCCFTV0ModelContractFreezeStage2OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.selectedBranch = "CP_NLSE" ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.governingEquationFrozen = true ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.frozenModelCount = 1 ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.newPostulateCount = 5 ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.referenceImplementationFrozen = true ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.mathematicalViabilityEstablished = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.physicalInterpretationEstablished = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.theoremAttempted = false ∧
    Derivation.ToeCCFTV0ModelContractFreezeResult.stageThreeAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
