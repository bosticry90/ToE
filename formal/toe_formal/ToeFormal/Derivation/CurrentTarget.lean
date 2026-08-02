import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := preparationTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PROPOSAL_PREPARED"
def currentBoundedProgramState : String := "PROPOSAL_PREPARED_UNINSTALLED"

theorem current_target_preserves_uninstalled_nonselecting_proposal :
    currentLiveTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧ proposedStageCount = 5 ∧
    programInstalled = false ∧ stageOneOpened = false ∧ branchSelected = false ∧
    ccftV0Constructed = false ∧ theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
