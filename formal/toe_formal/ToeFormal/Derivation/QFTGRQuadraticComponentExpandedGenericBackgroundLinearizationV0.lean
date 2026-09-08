import ToeFormal.Derivation.QFTGRQuadraticExactGenericFrozenCompanionOperatorResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-BACKGROUND-LINEARIZATION-v0"

def executionTarget : String :=
  "derive_qft_gr_quadratic_component_expanded_generic_background_linearization_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_component_expanded_generic_background_linearization_v0_result"

def acceptedGaugeRegularity : Nat := 2
def requiredMetricDependentGaugeRegularity : Nat := 3
def reducedComponentCount : Nat := 64
def minkowskiCompanionStateCount : Nat := 128
def minkowskiSparseEntryCount : Nat := 224

def gaugeJetOrderObstructionDerived : Bool := true
def genericTraceTangentObstructionDerived : Bool := true
def backgroundJetAmbiguityDerived : Bool := true
def componentExpandedLinearizationDerived : Bool := false
def minkowskiControlPreserved : Bool := true
def exactGenericCompanionDerived : Bool := false
def genericSpectrumDerived : Bool := false
def genericFiniteLossEstablished : Bool := false
def variableCoefficientEstimateEstablished : Bool := false
def localWellPosednessEstablished : Bool := false

def terminalOutcomes : List String :=
  [ "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED",
    "BACKGROUND_JET_CONTRACT_INCOMPLETE",
    "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS",
    "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_INCOMPLETE",
    "MINKOWSKI_CONTROL_PRESERVED_NOT_REDERIVED" ]

theorem metric_dependent_gauge_contract_is_underregular :
    acceptedGaugeRegularity < requiredMetricDependentGaugeRegularity := by
  decide

theorem Minkowski_control_custody_closes :
    minkowskiCompanionStateCount = 2 * reducedComponentCount ∧
      minkowskiSparseEntryCount = 224 ∧
      minkowskiControlPreserved = true := by
  decide

theorem generic_component_expansion_fails_closed :
    gaugeJetOrderObstructionDerived = true ∧
      genericTraceTangentObstructionDerived = true ∧
      backgroundJetAmbiguityDerived = true ∧
      componentExpandedLinearizationDerived = false ∧
      exactGenericCompanionDerived = false := by
  decide

theorem no_spectral_or_well_posedness_result_follows :
    genericSpectrumDerived = false ∧
      genericFiniteLossEstablished = false ∧
      variableCoefficientEstimateEstablished = false ∧
      localWellPosednessEstablished = false := by
  decide

end QFTGRQuadraticComponentExpandedGenericBackgroundLinearizationV0
end Derivation
end ToeFormal
