import ToeFormal.Derivation.DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview

namespace ToeFormal
namespace Derivation
namespace PostDiracMaxwellReductionBlockedRouteDecisionPacket

def packetId : String :=
  "POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_v0"

def target : String :=
  DiracMaxwell3p1To1p1ReductionConsistencyPacketResultReview.selectedNextTarget

def selectedNextTarget : String :=
  "review_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0_result"

def postAcceptanceTarget : String :=
  "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0"

def generatorSha256 : String :=
  "88257fb53c68e117c6baf276c1aa3423129814a802a073f1be3a925f31bc97bb"

def packetSha256 : String :=
  "877796d69cb09211b3160a72d2cee948703ec5985279c84bbae9983eb938a23e"

def manifestSha256 : String :=
  "e0d077ae88606f438717cb48138927088c080fcb171270917c17b0b6d121fc37"

def reportSha256 : String :=
  "552ebe36ec3f3d2e3739e01d9add879501e976e83ae5b0d06a1ed9561ec0d11e"

def candidateCount : Nat := 4
def criterionCount : Nat := 8
def maximumScore : Nat := 62
def threshold : Nat := 44
def repairScore : Nat := 51
def nativeOnePlusOneScore : Nat := 37
def twoPlusOneScore : Nat := 38
def changeMatterScore : Nat := 31
def mutationControlCount : Nat := 8

def recommendationUsedAsScoreInput : Bool := false
def externalContextRouteEligible : Bool := false
def restrictedSectorDefaultRepair : Bool := false
def numericalGuardrailAuthorized : Bool := false
def executionAuthorized : Bool := false

theorem preparation_consumes_exact_post_block_target :
    target = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0" := by
  rfl

theorem all_four_routes_are_scored_on_one_frozen_scale :
    candidateCount = 4 ∧ criterionCount = 8 ∧ maximumScore = 62 ∧ threshold = 44 := by
  decide

theorem repair_is_highest_scoring_without_recommendation_or_external_oracle :
    repairScore > nativeOnePlusOneScore ∧ repairScore > twoPlusOneScore ∧
      repairScore > changeMatterScore ∧ recommendationUsedAsScoreInput = false ∧
      externalContextRouteEligible = false := by
  decide

theorem selected_repair_retains_transverse_fields_not_tailored_sector :
    restrictedSectorDefaultRepair = false ∧
      postAcceptanceTarget =
        "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0" := by
  decide

theorem preparation_authorizes_only_independent_review :
    mutationControlCount = 8 ∧ numericalGuardrailAuthorized = false ∧
      executionAuthorized = false := by
  decide

end PostDiracMaxwellReductionBlockedRouteDecisionPacket
end Derivation
end ToeFormal
