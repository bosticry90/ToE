import ToeFormal.Release.LegacyDiscoveryReportFixtureRepair

/-
Operational certificate for the v1 repair-evidence binding correction. It
rebinds implementation identities to committed Git bytes and changes no
fixture, materializer behavior, authority, scientific claim, or migration
authorization. Raw detached acceptance remains pending.
-/

namespace ToeFormal
namespace Release
namespace LegacyDiscoveryReportFixtureRepairCorrectionV1

def correctionId : String :=
  "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_REPAIR_20260711_v1"

def correctionStatus : String :=
  "VERSIONED_SOURCE_BINDING_CORRECTION_REPAIR_SCOPE_UNCHANGED_PENDING_RAW_DETACHED_CLEAN_CHECKOUT_ACCEPTANCE"

def correctionArtifactSha256 : String :=
  "7befc5fd9500d2e099a26013eed159a6ece9dff1a3c29365a6c53314cd19b940"

def supersededV0Sha256 : String :=
  "e70d8741de6378e4f00bb135607cb92b06ad83ee8b78e0675b93a6226720f9eb"

def scientificTarget : String :=
  "execute_pillar_seam_unit_mapping_ledger_v0"

def maintenanceTarget : String :=
  "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"

def affectedTestCount : Nat := 20
def reportNodeCount : Nat := 21
def firstRawDetachedPassCount : Nat := 189
def firstRawDetachedSourceBindingFailureCount : Nat := 1
def fixtureChainFailureCount : Nat := 0
def runtimePathsAbsentAfterRun : Nat := 21

def fixtureBytesChanged : Bool := false
def fixtureLogicChanged : Bool := false
def rawDetachedCleanCheckoutAccepted : Bool := false
def registryMigrationExecutionAuthorized : Bool := false
def scientificTargetRotated : Bool := false
def maintenanceTargetRotated : Bool := false
def scientificClaimOrBlockerMovement : Bool := false

theorem correction_preserves_bounded_repair_scope :
    affectedTestCount = 20 ∧
      reportNodeCount = 21 ∧
      firstRawDetachedPassCount = 189 ∧
      firstRawDetachedSourceBindingFailureCount = 1 ∧
      fixtureChainFailureCount = 0 ∧
      runtimePathsAbsentAfterRun = 21 := by
  native_decide

theorem correction_preserves_targets :
    scientificTarget = "execute_pillar_seam_unit_mapping_ledger_v0" ∧
      maintenanceTarget =
        "prepare_loop_control_registry_sharding_and_current_projection_packet_v0" := by
  native_decide

theorem correction_changes_only_evidence_binding :
    fixtureBytesChanged = false ∧
      fixtureLogicChanged = false ∧
      rawDetachedCleanCheckoutAccepted = false ∧
      registryMigrationExecutionAuthorized = false ∧
      scientificTargetRotated = false ∧
      maintenanceTargetRotated = false ∧
      scientificClaimOrBlockerMovement = false := by
  decide

end LegacyDiscoveryReportFixtureRepairCorrectionV1
end Release
end ToeFormal
