namespace ToeFormal
namespace Release
namespace ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityV0

def authorityId : String :=
  "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN_AUTHORITY_v0"
def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION"
def frozenModelId : String := "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
def proposedPacketId : String :=
  "CCFT_V0_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_PACKET_v0"
def stageNumber : Nat := 3
def maximumPrimaryTheoremPackets : Nat := 1
def compoundClaimCount : Nat := 4
def frozenModelCount : Nat := 1
def newPostulateCount : Nat := 5
def stageThreeOpenAuthorized : Bool := true
def packetFrozen : Bool := false
def theoremProved : Bool := false
def theoremExecutionAuthorized : Bool := false
def modelMutationAuthorized : Bool := false
def physicalPromotionAuthorized : Bool := false
def stageFourAuthorized : Bool := false

theorem authority_opens_packet_preparation_without_theorem_result :
    stageNumber = 3 ∧ maximumPrimaryTheoremPackets = 1 ∧ compoundClaimCount = 4 ∧
    frozenModelCount = 1 ∧ newPostulateCount = 5 ∧ stageThreeOpenAuthorized = true ∧
    packetFrozen = false ∧ theoremProved = false ∧
    theoremExecutionAuthorized = false ∧ modelMutationAuthorized = false ∧
    physicalPromotionAuthorized = false ∧ stageFourAuthorized = false := by
  decide

end ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityV0
end Release
end ToeFormal
