namespace ToeFormal
namespace Derivation
namespace ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority

def authorityId : String :=
  "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_AUTHORITY_v0"
def reviewId : String :=
  "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_AUTHORITY_REVIEW_v0"
def executionTarget : String :=
  "select_post_ccft_core_recovery_development_route_v0"
def consumedTarget : String :=
  "close_toe_ccft_native_mathematical_core_and_operationalization_v0_after_bounded_result_v0"
def candidateRouteCount : Nat := 3
def authorizedInputCount : Nat := 4
def targetedRecoveryPassLimit : Nat := 1
def archiveTraversalAuthorized : Bool := false
def ccftV0ProgramPreparationAuthorized : Bool := false
def programInstalled : Bool := false
def programOpened : Bool := false
def newCCFTPostulateAuthorized : Bool := false
def scientificCalculationAuthorized : Bool := false
def evidencePromotionAuthorized : Bool := false
def automaticSecondSearchAuthorized : Bool := false

theorem authority_is_one_nonexecuting_route_decision :
    candidateRouteCount = 3 ∧ authorizedInputCount = 4 ∧
    targetedRecoveryPassLimit = 1 ∧ archiveTraversalAuthorized = false ∧
    ccftV0ProgramPreparationAuthorized = false ∧ programInstalled = false ∧
    programOpened = false ∧ newCCFTPostulateAuthorized = false ∧
    scientificCalculationAuthorized = false ∧ evidencePromotionAuthorized = false ∧
    automaticSecondSearchAuthorized = false := by
  decide

end ToePostCCFTCoreRecoveryDevelopmentRouteSelectionAuthority
end Derivation
end ToeFormal
