namespace ToeFormal
namespace Release
namespace ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityV0

def authorityId : String :=
  "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN_AUTHORITY_v0"
def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION"
def frozenModelId : String := "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
def frozenPacketId : String :=
  "CCFT_V0_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_PACKET_v0"
def stageNumber : Nat := 4
def frozenPacketCount : Nat := 1
def linkedClaimCount : Nat := 4
def formalPropositionCount : Nat := 4
def formalNegationCount : Nat := 4
def executionContractCount : Nat := 3
def stageFourOpenAuthorized : Bool := true
def theoremResultCount : Nat := 0
def modelMutationAuthorized : Bool := false
def packetMutationAuthorized : Bool := false
def newPostulateAuthorized : Bool := false
def physicalPromotionAuthorized : Bool := false
def stageFiveAuthorized : Bool := false

theorem authority_opens_exact_attack_execution_without_a_result :
    stageNumber = 4 ∧ frozenPacketCount = 1 ∧ linkedClaimCount = 4 ∧
    formalPropositionCount = 4 ∧ formalNegationCount = 4 ∧
    executionContractCount = 3 ∧ stageFourOpenAuthorized = true ∧
    theoremResultCount = 0 ∧ modelMutationAuthorized = false ∧
    packetMutationAuthorized = false ∧ newPostulateAuthorized = false ∧
    physicalPromotionAuthorized = false ∧ stageFiveAuthorized = false := by
  decide

end ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityV0
end Release
end ToeFormal
