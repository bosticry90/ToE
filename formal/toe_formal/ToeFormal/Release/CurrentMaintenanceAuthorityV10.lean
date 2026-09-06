import ToeFormal.Release.ToeRepositoryWideNativeHypothesisCensusIndexingAndPerformanceMaintenanceResultReviewV0

namespace ToeFormal
namespace Release
namespace CurrentMaintenanceAuthorityV10

open ToeRepositoryWideNativeHypothesisCensusIndexingAndPerformanceMaintenanceResultV0
open ToeRepositoryWideNativeHypothesisCensusIndexingAndPerformanceMaintenanceResultReviewV0

def authorityId : String := "CURRENT_MAINTENANCE_AUTHORITY_v10"

def completedMaintenanceTarget : String :=
  "review_toe_repository_wide_native_hypothesis_census_indexing_and_performance_maintenance_result_v0"

def nextDecision : String :=
  "SEPARATE_SCIENTIFIC_AUTHORITY_DECISION_FOR_REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1"

def scientificTargetRotated : Bool := false

theorem maintenance_closed_without_opening_science :
    reviewAccepted = true ∧
    maintenanceComplete = true ∧
    programOpened = false ∧
    stageOneAttempted = false ∧
    stageOneScientificAuthorityGranted = false ∧
    scientificTargetRotated = false := by
  decide

end CurrentMaintenanceAuthorityV10
end Release
end ToeFormal
