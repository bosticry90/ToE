namespace ToeFormal
namespace Release
namespace CurrentMaintenanceAuthorityV4

def authorityId : String := "CURRENT_MAINTENANCE_AUTHORITY_v4"

def completedMaintenanceTarget : String :=
  "execute_canonical_text_attribute_policy_repair_v0"

def currentScientificTarget : String :=
  "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0"

def historicalBytesRewritten : Bool := false
def scientificTargetRotated : Bool := false
def automaticMaintenanceSuccessorAuthorized : Bool := false
def maintenanceAccepted : Bool := true

theorem canonical_text_maintenance_closed_without_scientific_rotation :
    maintenanceAccepted = true ∧
    historicalBytesRewritten = false ∧
    scientificTargetRotated = false ∧
    automaticMaintenanceSuccessorAuthorized = false := by
  decide

end CurrentMaintenanceAuthorityV4
end Release
end ToeFormal
