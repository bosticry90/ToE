import ToeFormal.Release.ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityReviewV0
import ToeFormal.Release.ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityV0

namespace ToeFormal
namespace Derivation
namespace ToeNativeGravitationalRequirementInventoryAttemptOpen

def eventId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0_ATTEMPT_01_OPEN_v0"

def programId : String :=
  "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"

def semanticStageId : String :=
  "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY"

def scientificTarget : String :=
  "inventory_toe_native_gravitational_requirements_v0"

def scopeHash : String :=
  "297276852be0fed5e7dafdb9a90a3dc26a2807665665dbefc69dd8572b31fb19"

def attemptNumber : Nat := 1
def programOpen : Bool := true
def scientificResultCreated : Bool := false
def requirementRowsAdjudicated : Nat := 0
def actionFamiliesCompared : Bool := false
def evidencePromoted : Bool := false
def gravitationalActionSelected : Bool := false
def nativeGravitationalPrincipleSelected : Bool := false
def gravitationalCalculationStarted : Bool := false
def stageTwoAuthorized : Bool := false

theorem stage_one_is_open_without_scientific_output :
    Release.ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityV0.authorityGranted =
      true ∧
    Release.ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityReviewV0.authorityAccepted =
      true ∧
    attemptNumber = 1 ∧
    programOpen = true ∧
    scientificResultCreated = false ∧
    requirementRowsAdjudicated = 0 ∧
    actionFamiliesCompared = false ∧
    evidencePromoted = false ∧
    gravitationalActionSelected = false ∧
    nativeGravitationalPrincipleSelected = false ∧
    gravitationalCalculationStarted = false ∧
    stageTwoAuthorized = false := by
  decide

end ToeNativeGravitationalRequirementInventoryAttemptOpen
end Derivation
end ToeFormal
