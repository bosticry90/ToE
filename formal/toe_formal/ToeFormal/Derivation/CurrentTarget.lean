import ToeFormal.Derivation.ToeCCFTV0BranchReadinessAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0BranchReadinessAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_BRANCH_READINESS_STAGE_1_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_1"

theorem current_target_is_nonselecting_stage_one_open :
    attemptNumber = 1 ∧ branchSelected = false ∧ modelConstructed = false ∧
    postulateCreated = false ∧ theoremPacketPrepared = false ∧
    theoremAttempted = false ∧ stageTwoAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
