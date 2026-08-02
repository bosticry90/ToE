import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionProgramInstallationAuthority
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_INSTALLATION_AUTHORIZED"
def currentBoundedProgramState : String := "INSTALLATION_AUTHORIZED_NOT_EXECUTED"

theorem current_target_authorizes_installation_without_science :
    installationAuthorized = true ∧ scientificStageOpenAuthorized = false ∧
    branchSelected = false ∧ modelConstructed = false ∧ theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
