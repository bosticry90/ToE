import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_is_ccft_v0_program_preparation_only :
    currentTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.proposalPreparationAuthorized = true ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.programInstallationAuthorized = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.theoremDiscoveryAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
