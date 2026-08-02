import ToeFormal.Derivation.ToeCCFTV0ModelContractFreezeResult

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0ModelContractFreezeResult
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := proposedStageThreeTarget
def currentEvidencePacketId : String := resultId
def currentTargetPhase : String := "CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_STAGE_2_CLOSED_PASSED"
def currentBoundedProgramState : String := "CLOSED_AWAITING_SEPARATE_STAGE_3_AUTHORITY"

theorem current_target_is_nonautomatic_stage_three_preparation :
    selectedBranch = "CP_NLSE" ∧ attemptSequenceNumber = 2 ∧
    frozenModelCount = 1 ∧ governingEquationFrozen = true ∧
    newPostulateCount = 5 ∧ referenceImplementationFrozen = true ∧
    theoremPacketPrepared = false ∧ theoremAttempted = false ∧
    stageThreeAuthorized = false ∧ mathematicalViabilityEstablished = false ∧
    physicalInterpretationEstablished = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
