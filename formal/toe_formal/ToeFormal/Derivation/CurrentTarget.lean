import ToeFormal.Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0PrimaryTheoremPacketAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_3"

theorem current_target_is_empty_stage_three_open :
    attemptNumber = 3 ∧ maximumPrimaryTheoremPackets = 1 ∧
    proposedCompoundClaimCount = 4 ∧ frozenPacketCount = 0 ∧
    frozenPropositionCount = 0 ∧ frozenFormalNegationCount = 0 ∧
    executionContractCount = 0 ∧ theoremResultCount = 0 ∧
    counterexampleCount = 0 ∧ modelMutated = false ∧
    historicalFormulaClassified = false ∧ physicalPromotion = false ∧
    stageFourAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
