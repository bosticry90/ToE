import ToeFormal.Derivation.CCFTToTOEObjectCrosswalkPacket

namespace ToeFormal
namespace Derivation
namespace CCFTCKAdmissibilityObligationIndexPacket

set_option linter.style.longLine false

def packetId : String := "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_v0"

def packetResult : String :=
  "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_SOURCE_BRIDGE_TRANSPORT_EXCHANGE_ROWS_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"

def strictPacketResult : String :=
  "CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_PACKET_PREPARED_CCFT_SPECIFIC_CK_OBLIGATIONS_ONLY_NO_CCFT_VALIDATION_OR_CK_RULE_PROMOTION"

def outcomeId : String := packetResult

def consumedTarget : String :=
  CCFTToTOEObjectCrosswalkPacket.selectedNextTarget

def selectedNextTarget : String :=
  "review_ccft_ck_admissibility_obligation_index_packet_result"

def selectedNextTargetKind : String :=
  "ccft_ck_admissibility_obligation_index_packet_result_review"

def proofAttemptExecuted : Bool := false
def theoremDischarged : Bool := false
def rulePromoted : Bool := false
def ccftValidated : Bool := false
def pillarClosureClaim : Bool := false
def seamClosureClaim : Bool := false
def masterActionPromoted : Bool := false

def leanStatusWording : String :=
  "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION; scoped Lean targets = PASSED_SERIAL_RERUN"

theorem ccft_ck_index_rotates_to_review :
    selectedNextTarget = "review_ccft_ck_admissibility_obligation_index_packet_result" := by
  rfl

end CCFTCKAdmissibilityObligationIndexPacket
end Derivation
end ToeFormal
