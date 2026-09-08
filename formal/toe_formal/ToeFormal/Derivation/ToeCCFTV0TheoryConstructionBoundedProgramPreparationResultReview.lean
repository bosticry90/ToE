import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview

def resultId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0"
def directorPacketId : String := "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0"
def preparationTarget : String := "prepare_bounded_ccft_v0_theory_construction_program"
def proposedProgramId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def proposedMandatoryExit : String := "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_after_bounded_result_v0"
def proposedStageCount : Nat := 5
def directorOptionCount : Nat := 4
def provenanceLabelCount : Nat := 5
def maximumFrozenModels : Nat := 1
def maximumPrimaryTheoremPackets : Nat := 1
def programInstalled : Bool := false
def stageOneOpened : Bool := false
def branchSelected : Bool := false
def ccftV0Constructed : Bool := false
def theoremAttempted : Bool := false

theorem proposal_is_bounded_science_centered_and_uninstalled :
    proposedStageCount = 5 ∧ directorOptionCount = 4 ∧ provenanceLabelCount = 5 ∧
    maximumFrozenModels = 1 ∧ maximumPrimaryTheoremPackets = 1 ∧
    programInstalled = false ∧ stageOneOpened = false ∧ branchSelected = false ∧
    ccftV0Constructed = false ∧ theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview
end Derivation
end ToeFormal
