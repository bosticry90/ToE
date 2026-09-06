import ToeFormal.Derivation.QFTGRQuadraticFrozenCoefficientJordanChainFrequencyGrowthResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticExactGenericFrozenCompanionOperatorV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-OPERATOR-v0"

def executionTarget : String :=
  "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_exact_generic_frozen_companion_operator_v0_result"

def reducedComponentCount : Nat := 64
def companionStateCount : Nat := 128
def minkowskiSparseEntryCount : Nat := 224
def genericExpansionBlockerCount : Nat := 5

def exactMinkowskiControlDerived : Bool := true
def exactGenericBackgroundOperatorDerived : Bool := false
def genericCharacteristicAsymptoticsDerived : Bool := false
def genericFiniteLossEstablished : Bool := false
def genericFractionalRootSplittingExcluded : Bool := false
def constraintTangentProjectorConstructed : Bool := false
def variableCoefficientEstimateEstablished : Bool := false
def localWellPosednessEstablished : Bool := false

def terminalOutcomes : List String :=
  [ "MINKOWSKI_FROZEN_COMPANION_OPERATOR_EXACTLY_DERIVED_CONTROL_ONLY",
    "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED",
    "GENERIC_SUBPRINCIPAL_SPECTRAL_CLASSIFICATION_NOT_AUTHORIZED",
    "CONSTRAINT_TANGENT_PROJECTOR_REMAINS_BLOCKED" ]

theorem companion_dimensions_close :
    companionStateCount = 2 * reducedComponentCount := by
  decide

theorem minkowski_control_is_exact_but_not_generic :
    exactMinkowskiControlDerived = true ∧
      minkowskiSparseEntryCount = 224 ∧
      exactGenericBackgroundOperatorDerived = false := by
  decide

theorem generic_operator_and_spectrum_fail_closed :
    genericExpansionBlockerCount = 5 ∧
      genericCharacteristicAsymptoticsDerived = false ∧
      genericFiniteLossEstablished = false ∧
      genericFractionalRootSplittingExcluded = false ∧
      constraintTangentProjectorConstructed = false := by
  decide

theorem no_variable_or_nonlinear_theorem_follows :
    variableCoefficientEstimateEstablished = false ∧
      localWellPosednessEstablished = false := by
  decide

end QFTGRQuadraticExactGenericFrozenCompanionOperatorV0
end Derivation
end ToeFormal
