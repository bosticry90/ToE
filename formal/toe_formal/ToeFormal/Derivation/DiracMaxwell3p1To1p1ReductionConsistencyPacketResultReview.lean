import ToeFormal.Derivation.DiracMaxwell3p1To1p1ReductionConsistencyPacket

namespace ToeFormal
namespace Derivation
namespace DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview

def reviewId : String :=
  "DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0"

def consumedTarget : String :=
  DiracMaxwell3p1To1p1ReductionConsistencyPacket.selectedNextTarget

def verdict : String := "B-BLOCKED"

def blockerCode : String :=
  "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT"

def selectedNextTarget : String :=
  "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0"

def preparationCommit : String :=
  "8aa48069db94082bdb639719b549466bd92862cd"

def preparationParent : String :=
  "113dee3c4026334c535b4ba994ddb170abd0c9fe"

def reviewerSha256 : String :=
  "0262b6bd9a6b463a988c3345f041cbc3341898242afbb9d007b03618c283d28a"

def reviewReportSha256 : String :=
  "3f2879163b5e8e90fba286eacdbdebdfdf3ce5b043169ade5f5b8db41b95eec6"

def decisionCount : Nat := 14
def passedDecisionCount : Nat := 14
def reviewAccepted : Bool := true
def boundedBlockerAccepted : Bool := true
def reductionAccepted : Bool := false
def routeDecisionPreparationAuthorized : Bool := true
def numericalGuardrailAuthorized : Bool := false
def executionAuthorized : Bool := false
def fallbackSelectedAutomatically : Bool := false

theorem review_consumes_exact_reduction_review_target :
    consumedTarget =
      "review_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0_result" := by
  rfl

theorem independent_review_accepts_the_blocker_not_the_reduction :
    reviewAccepted = true ∧ boundedBlockerAccepted = true ∧
      verdict = "B-BLOCKED" ∧
      blockerCode = "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT" ∧
      reductionAccepted = false := by
  decide

theorem review_selects_only_post_block_route_decision_preparation :
    selectedNextTarget =
        "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0" ∧
      routeDecisionPreparationAuthorized = true ∧
      numericalGuardrailAuthorized = false ∧ executionAuthorized = false ∧
      fallbackSelectedAutomatically = false := by
  decide

theorem review_recomputes_all_decisions :
    decisionCount = 14 ∧ passedDecisionCount = 14 := by
  decide

end DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview
end Derivation
end ToeFormal
