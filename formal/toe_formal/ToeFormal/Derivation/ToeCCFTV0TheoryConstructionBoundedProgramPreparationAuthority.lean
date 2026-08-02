namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

def authorityId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String := "prepare_bounded_ccft_v0_theory_construction_program"
def proposalPreparationAuthorized : Bool := true
def recoveredContractCount : Nat := 4
def preservedConflictCount : Nat := 3
def directorOptionCount : Nat := 4
def programInstallationAuthorized : Bool := false
def branchSelectionAuthorized : Bool := false
def newPostulateAuthorized : Bool := false
def theoremDiscoveryAuthorized : Bool := false

theorem authority_is_nonexecuting_program_preparation_only :
    proposalPreparationAuthorized = true ∧ recoveredContractCount = 4 ∧
    preservedConflictCount = 3 ∧ directorOptionCount = 4 ∧
    programInstallationAuthorized = false ∧ branchSelectionAuthorized = false ∧
    newPostulateAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority
end Derivation
end ToeFormal
