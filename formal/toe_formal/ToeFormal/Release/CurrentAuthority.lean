import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_preserves_closed_stage_one_without_stage_two_authority :
    currentTarget = "complete_and_freeze_toe_ccft_v0_model_contract_v0" ∧
    currentBoundedProgramState = "CLOSED" ∧
    Derivation.ToeCCFTV0BranchReadinessResult.selectedBranch = "CP_NLSE" ∧
    Derivation.ToeCCFTV0BranchReadinessResult.governingEquationSelected = false ∧
    Derivation.ToeCCFTV0BranchReadinessResult.modelConstructed = false ∧
    Derivation.ToeCCFTV0BranchReadinessResult.stageTwoAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
