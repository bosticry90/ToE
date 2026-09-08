import ToeFormal.Release.ToeNativeCoherenceOntologyProgramGovernanceInstallationV0

namespace ToeFormal
namespace Release
namespace CurrentMaintenanceAuthorityV8

def authorityId : String := "CURRENT_MAINTENANCE_AUTHORITY_v8"

def completedMaintenanceTarget : String :=
  "review_toe_native_coherence_ontology_program_governance_installation_result_v0"

def currentScientificTarget : String :=
  ToeNativeCoherenceOntologyProgramGovernanceInstallationV0.preservedScientificTarget

def programId : String :=
  ToeNativeCoherenceOntologyProgramGovernanceInstallationV0.programId

def maintenanceAccepted : Bool := true
def programInstalled : Bool := true
def programOpened : Bool := false
def scientificTargetRotated : Bool := false
def automaticMaintenanceSuccessorAuthorized : Bool := false

theorem installation_closed_with_program_unopened :
    maintenanceAccepted = true ∧
    programInstalled = true ∧
    programOpened = false ∧
    scientificTargetRotated = false ∧
    automaticMaintenanceSuccessorAuthorized = false := by
  decide

end CurrentMaintenanceAuthorityV8
end Release
end ToeFormal
