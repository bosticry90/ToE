namespace ToeFormal
namespace Derivation
namespace ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationAuthority

def authorityId : String :=
  "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0"
def reviewId : String :=
  "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String :=
  "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0"
def selectedFrontier : String :=
  "HYP_TOE_CCFT_MINIMAL_NATIVE_MATHEMATICAL_CORE_OPERATIONALIZATION_v0"
def proposalPreparationAuthorized : Bool := true
def programInstalled : Bool := false
def scientificStageOpened : Bool := false
def ccftMathematicsRecoveredOrAdjudicated : Bool := false
def ccftRepresentationOrFieldSelected : Bool := false
def ccftActionConstructed : Bool := false
def ccftSeamOrObservableSelected : Bool := false
def evidencePromoted : Bool := false
def scientificSuccessorAuthorized : Bool := false

theorem authority_is_exactly_nonexecuting_proposal_preparation :
    authorizedTarget =
      "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0" ∧
    selectedFrontier =
      "HYP_TOE_CCFT_MINIMAL_NATIVE_MATHEMATICAL_CORE_OPERATIONALIZATION_v0" ∧
    proposalPreparationAuthorized = true ∧ programInstalled = false ∧
    scientificStageOpened = false ∧
    ccftMathematicsRecoveredOrAdjudicated = false ∧
    ccftRepresentationOrFieldSelected = false ∧ ccftActionConstructed = false ∧
    ccftSeamOrObservableSelected = false ∧ evidencePromoted = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end ToeCCFTNativeMathematicalCoreAndOperationalizationBoundedProgramPreparationAuthority
end Derivation
end ToeFormal
