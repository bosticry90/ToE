import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PREPARATION_AUTHORIZED"
def currentBoundedProgramState : String := "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"

theorem current_target_authorizes_preparation_without_scientific_execution :
    currentLiveTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧ proposalPreparationAuthorized = true ∧
    programInstallationAuthorized = false ∧ branchSelectionAuthorized = false ∧
    newPostulateAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
