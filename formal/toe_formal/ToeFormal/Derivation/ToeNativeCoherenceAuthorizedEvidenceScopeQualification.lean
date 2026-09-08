namespace ToeFormal
namespace Derivation
namespace ToeNativeCoherenceAuthorizedEvidenceScopeQualification

def calculationId : String :=
  "CALC-TOE-NATIVE-COHERENCE-AUTHORIZED-EVIDENCE-SCOPE-QUALIFICATION-v0"

def authorizedSourceCount : Nat := 13
def archiveWideCensusPerformed : Bool := false
def repositoryWideEvidenceTested : Bool := false
def everyRepositoryClaimExhausted : Bool := false
def futureRepresentationRuledOut : Bool := false
def closedProgramReopened : Bool := false
def closedOutcomeChanged : Bool := false

def authorizedEvidenceStatus : String :=
  "FAILED"

def repositoryWideEvidenceStatus : String :=
  "NOT_TESTED"

theorem qualification_is_narrow_and_non_reopening :
    authorizedSourceCount = 13 ∧
    archiveWideCensusPerformed = false ∧
    repositoryWideEvidenceTested = false ∧
    everyRepositoryClaimExhausted = false ∧
    futureRepresentationRuledOut = false ∧
    closedProgramReopened = false ∧
    closedOutcomeChanged = false := by
  decide

theorem qualification_preserves_the_closed_result :
    authorizedEvidenceStatus = "FAILED" ∧
    repositoryWideEvidenceStatus = "NOT_TESTED" := by
  decide

end ToeNativeCoherenceAuthorizedEvidenceScopeQualification
end Derivation
end ToeFormal
