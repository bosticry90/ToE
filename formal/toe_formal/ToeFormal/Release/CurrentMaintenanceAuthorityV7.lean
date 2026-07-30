namespace ToeFormal
namespace Release
namespace CurrentMaintenanceAuthorityV7

def authorityId : String := "CURRENT_MAINTENANCE_AUTHORITY_v7"

def maintenanceTarget : String :=
  "install_toe_native_coherence_ontology_and_representation_bounded_program_governance_v0"

def currentScientificTarget : String :=
  "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"

def proposedProgramId : String :=
  "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"

def maintenanceAuthorized : Bool := true
def scientificTargetRotated : Bool := false
def programOpenAuthorized : Bool := false
def scientificOutputAuthorized : Bool := false

theorem governance_installation_authority_is_unopened_and_non_scientific :
    maintenanceAuthorized = true ∧
    scientificTargetRotated = false ∧
    programOpenAuthorized = false ∧
    scientificOutputAuthorized = false := by
  decide

end CurrentMaintenanceAuthorityV7
end Release
end ToeFormal
