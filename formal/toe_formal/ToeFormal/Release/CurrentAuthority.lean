import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_is_installation_only :
    currentTarget = "install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0" ∧
    Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority.installationAuthorized = true ∧
    Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority.scientificStageOpenAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
