namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionProgramInstallationAuthority

def authorityId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String := "install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0"
def installationAuthorized : Bool := true
def authorizedStageCount : Nat := 5
def attemptCap : Nat := 5
def repairAttemptCount : Nat := 0
def scientificStageOpenAuthorized : Bool := false
def branchSelected : Bool := false
def modelConstructed : Bool := false
def theoremAttempted : Bool := false

theorem authority_is_installation_only :
    installationAuthorized = true ∧ authorizedStageCount = 5 ∧ attemptCap = 5 ∧
    repairAttemptCount = 0 ∧ scientificStageOpenAuthorized = false ∧
    branchSelected = false ∧ modelConstructed = false ∧ theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionProgramInstallationAuthority
end Derivation
end ToeFormal
