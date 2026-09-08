namespace ToeFormal
namespace Release
namespace ToeCCFTV0TheoryConstructionProgramGovernanceInstallation

def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def manifestPath : String := "formal/docs/release/bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
def mandatoryExit : String := "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_after_bounded_result_v0"
def authorizedStageCount : Nat := 5
def attemptCap : Nat := 5
def repairAttemptCount : Nat := 0
def scientificAttempts : Nat := 0
def eventCount : Nat := 0
def maximumFrozenModels : Nat := 1
def maximumNewPostulates : Nat := 8
def maximumPrimaryTheoremPackets : Nat := 1
def installedUnopened : Bool := true
def branchSelected : Bool := false
def modelConstructed : Bool := false
def theoremAttempted : Bool := false

theorem installation_is_bounded_and_scientifically_unopened :
    authorizedStageCount = 5 ∧ attemptCap = 5 ∧ repairAttemptCount = 0 ∧
    scientificAttempts = 0 ∧ eventCount = 0 ∧ maximumFrozenModels = 1 ∧
    maximumNewPostulates = 8 ∧ maximumPrimaryTheoremPackets = 1 ∧
    installedUnopened = true ∧ branchSelected = false ∧ modelConstructed = false ∧
    theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionProgramGovernanceInstallation
end Release
end ToeFormal
