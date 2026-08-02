import ToeFormal.Derivation.ToeCCFTV0BranchReadinessResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0BranchReadinessResult
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := proposedStageTwoTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_BRANCH_READINESS_STAGE_1_CLOSED_PASSED"
def currentBoundedProgramState : String := "CLOSED"

theorem current_target_is_unopened_stage_two_after_cp_nlse_route_selection :
    currentLiveTarget = "complete_and_freeze_toe_ccft_v0_model_contract_v0" ∧
    attemptSequenceNumber = 1 ∧ selectedBranch = "CP_NLSE" ∧
    governingEquationSelected = false ∧ newPostulateCreated = false ∧
    modelConstructed = false ∧ theoremSelectedOrAttempted = false ∧
    stageTwoAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
