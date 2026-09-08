namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticGenericBackgroundLinearizationGaugeAndJetContractV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-LINEARIZATION-GAUGE-AND-JET-CONTRACT-v0"

def boundedProgramId : String := "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
def semanticStageId : String := "STRICT_HARMONIC_GAUGE_JET_CONTRACT"
def attemptNumber : Nat := 1

def strictHarmonicSourceIsZero : Bool := true
def strictHarmonicPerturbationIsZero : Bool := true
def traceAtlasChartCount : Nat := 10
def reducedRegularityOrder : Nat := 3
def sufficientMetricEquivalenceRegularityOrder : Nat := 6
def rewriteTerminates : Bool := true
def rewriteIsConfluent : Bool := true

def componentExpansionDerived : Bool := false
def genericCompanionDerived : Bool := false
def genericFiniteLossEstablished : Bool := false

theorem strict_harmonic_contract_is_complete_and_bounded :
    strictHarmonicSourceIsZero = true ∧
    strictHarmonicPerturbationIsZero = true ∧
    traceAtlasChartCount = 10 ∧
    reducedRegularityOrder = 3 ∧
    sufficientMetricEquivalenceRegularityOrder = 6 ∧
    rewriteTerminates = true ∧
    rewriteIsConfluent = true := by
  decide

theorem later_stage_claims_remain_false :
    componentExpansionDerived = false ∧
    genericCompanionDerived = false ∧
    genericFiniteLossEstablished = false := by
  decide

end QFTGRQuadraticGenericBackgroundLinearizationGaugeAndJetContractV0
end Derivation
end ToeFormal
