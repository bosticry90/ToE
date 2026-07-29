namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticToeRoleAfterGenericFrozenResultV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-TOE-ROLE-AFTER-GENERIC-FROZEN-RESULT-v0"

def toeRole : String := "REFERENCE_CONTROL_ONLY"
def controlResult : String := "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
def attemptedStageCount : Nat := 3
def authorizedStageCount : Nat := 5
def repairAttemptCount : Nat := 0
def furtherQuadraticWorkAuthorized : Bool := false
def nativeProgramInstalledHere : Bool := false

theorem role_and_mathematical_result_are_separate :
    toeRole = "REFERENCE_CONTROL_ONLY" ∧
    controlResult = "UNRESOLVED_AFTER_BOUNDED_ATTEMPT" := by
  decide

theorem bounded_closeout_stops_without_repair :
    attemptedStageCount = 3 ∧
    authorizedStageCount = 5 ∧
    repairAttemptCount = 0 ∧
    furtherQuadraticWorkAuthorized = false ∧
    nativeProgramInstalledHere = false := by
  decide

end QFTGRQuadraticToeRoleAfterGenericFrozenResultV0
end Derivation
end ToeFormal
