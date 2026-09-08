namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationV1

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-BACKGROUND-LINEARIZATION-v1"

def boundedProgramId : String := "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
def semanticStageId : String := "COMPONENT_EXPANDED_LINEARIZATION"
def attemptNumber : Nat := 2

def componentDagNodeCount : Nat := 3950
def commonEquationCount : Nat := 55
def traceAtlasChartCount : Nat := 10
def tracefreeEquationCountPerChart : Nat := 9
def independentEquationCountPerChart : Nat := 64
def minkowskiStateCount : Nat := 128
def minkowskiNonzeroEntryCount : Nat := 224

def genericCompanionDerived : Bool := false
def genericFiniteLossEstablished : Bool := false

theorem component_inventory_and_Minkowski_regression_are_bounded :
    commonEquationCount + tracefreeEquationCountPerChart =
      independentEquationCountPerChart ∧
    traceAtlasChartCount = 10 ∧
    minkowskiStateCount = 128 ∧
    minkowskiNonzeroEntryCount = 224 := by
  decide

theorem later_stage_claims_remain_false :
    genericCompanionDerived = false ∧
    genericFiniteLossEstablished = false := by
  decide

end QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationV1
end Derivation
end ToeFormal
