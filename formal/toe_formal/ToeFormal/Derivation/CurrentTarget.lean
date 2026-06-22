import ToeFormal.Derivation.ToeNativeAVacuumSourceAdmissibilityIdentityPacket

/-
Thin current-target aggregate for tiered validation. This target follows the
live strict target and avoids requiring a full ToeFormal aggregate build for
routine packet checks.
-/

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"

def currentLiveTarget : String :=
  ToeNativeAVacuumSourceAdmissibilityIdentityPacket.selectedNextTarget

def currentEvidencePacketId : String :=
  ToeNativeAVacuumSourceAdmissibilityIdentityPacket.packetId

theorem current_target_points_to_a_vacuum_source_admissibility_identity_result_review :
    currentLiveTarget =
      "review_toe_native_A_vacuum_source_admissibility_identity_packet_result" := by
  rfl

end CurrentTarget
end Derivation
end ToeFormal
