import ToeFormal.Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallationReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := "install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0"
def currentEvidencePacketId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_REVIEW_v0"
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_INSTALLED_UNOPENED"
def currentBoundedProgramState : String := "INSTALLED_UNOPENED"

theorem current_target_preserves_unopened_installation :
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.installedUnopened = true ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.scientificAttempts = 0 ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.branchSelected = false ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.modelConstructed = false ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
