import ToeFormal.Release.BoundedProgramGovernanceEnforcementCompletionResultReviewV0

namespace ToeFormal
namespace Release
namespace CurrentMaintenanceAuthorityV6

def authorityId : String := "CURRENT_MAINTENANCE_AUTHORITY_v6"

def completedMaintenanceTarget : String :=
  "review_bounded_program_governance_enforcement_completion_maintenance_result_v0"

def currentScientificTarget : String :=
  "close_toe_native_surrogate_v0_after_bounded_result_v0"

def maintenanceAccepted : Bool :=
  BoundedProgramGovernanceEnforcementCompletionResultReviewV0.accepted

def scientificTargetRotated : Bool := false
def automaticMaintenanceSuccessorAuthorized : Bool := false

theorem enforcement_completion_closed_without_scientific_rotation :
    maintenanceAccepted = true ∧
    scientificTargetRotated = false ∧
    automaticMaintenanceSuccessorAuthorized = false := by
  decide

end CurrentMaintenanceAuthorityV6
end Release
end ToeFormal
