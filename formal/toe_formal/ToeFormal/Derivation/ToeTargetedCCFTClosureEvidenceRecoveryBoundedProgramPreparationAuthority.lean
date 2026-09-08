namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationAuthority

def authorityId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0"
def reviewId : String :=
  "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String :=
  "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0"
def postRecoveryConstructionPreparationTarget : String :=
  "prepare_bounded_ccft_v0_theory_construction_program"
def proposalPreparationAuthorized : Bool := true
def targetedRecoveryPassLimit : Nat := 1
def evidenceClassificationCount : Nat := 7
def terminalOutcomeCount : Nat := 2
def archiveTraversalAuthorized : Bool := false
def targetedRecoveryProgramInstalled : Bool := false
def scientificStageOpened : Bool := false
def ccftEquationRepairedOrSelected : Bool := false
def newCCFTPostulateInserted : Bool := false
def ccftV0ConstructionPreparationAuthorized : Bool := false
def automaticSecondSearchAuthorized : Bool := false

theorem authority_is_exactly_nonexecuting_proposal_preparation :
    authorizedTarget =
      "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0" ∧
    proposalPreparationAuthorized = true ∧ targetedRecoveryPassLimit = 1 ∧
    evidenceClassificationCount = 7 ∧ terminalOutcomeCount = 2 ∧
    archiveTraversalAuthorized = false ∧ targetedRecoveryProgramInstalled = false ∧
    scientificStageOpened = false ∧ ccftEquationRepairedOrSelected = false ∧
    newCCFTPostulateInserted = false ∧
    ccftV0ConstructionPreparationAuthorized = false ∧
    automaticSecondSearchAuthorized = false := by
  decide

end ToeTargetedCCFTClosureEvidenceRecoveryBoundedProgramPreparationAuthority
end Derivation
end ToeFormal
