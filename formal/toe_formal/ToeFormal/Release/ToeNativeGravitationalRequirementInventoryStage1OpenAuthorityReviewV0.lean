namespace ToeFormal
namespace Release
namespace ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityReviewV0

def authorityAccepted : Bool := true
def scientificResultCreated : Bool := false
def stageTwoAuthorized : Bool := false
def candidateFamiliesCompared : Bool := false
def actionSelected : Bool := false

theorem reviewed_authority_remains_open_only :
    authorityAccepted = true ∧
    scientificResultCreated = false ∧
    stageTwoAuthorized = false ∧
    candidateFamiliesCompared = false ∧
    actionSelected = false := by
  decide

end ToeNativeGravitationalRequirementInventoryStage1OpenAuthorityReviewV0
end Release
end ToeFormal
