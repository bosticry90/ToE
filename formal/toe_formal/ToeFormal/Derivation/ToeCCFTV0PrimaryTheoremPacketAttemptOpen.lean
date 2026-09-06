namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0PrimaryTheoremPacketAttemptOpen

def programId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
def semanticStageId : String := "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION"
def target : String := "prepare_toe_ccft_v0_primary_theorem_or_counterexample_packet_v0"
def frozenModelId : String := "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
def proposedPacketId : String := "CCFT_V0_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_PACKET_v0"
def scopeHash : String := "b0db245201d0fdc6edc15a8ac6028c01725ef4a0e2e87c53f9835094df1fe506"
def eventHash : String := "770b3dd74b80d0afb8613d79e7ba2e1ce286146e0d92c5c10c9ebf3e082e9caf"
def openedFromCommit : String := "ab7a31241c213fb1ad8042782af492c174322ded"
def attemptNumber : Nat := 3
def maximumPrimaryTheoremPackets : Nat := 1
def proposedCompoundClaimCount : Nat := 4
def frozenPacketCount : Nat := 0
def frozenPropositionCount : Nat := 0
def frozenFormalNegationCount : Nat := 0
def executionContractCount : Nat := 0
def theoremResultCount : Nat := 0
def counterexampleCount : Nat := 0
def modelMutated : Bool := false
def historicalFormulaClassified : Bool := false
def physicalPromotion : Bool := false
def stageFourAuthorized : Bool := false

theorem immutable_open_contains_no_packet_or_theorem_output :
    attemptNumber = 3 ∧ maximumPrimaryTheoremPackets = 1 ∧
    proposedCompoundClaimCount = 4 ∧ frozenPacketCount = 0 ∧
    frozenPropositionCount = 0 ∧ frozenFormalNegationCount = 0 ∧
    executionContractCount = 0 ∧ theoremResultCount = 0 ∧
    counterexampleCount = 0 ∧ modelMutated = false ∧
    historicalFormulaClassified = false ∧ physicalPromotion = false ∧
    stageFourAuthorized = false := by
  decide

end ToeCCFTV0PrimaryTheoremPacketAttemptOpen
end Derivation
end ToeFormal
