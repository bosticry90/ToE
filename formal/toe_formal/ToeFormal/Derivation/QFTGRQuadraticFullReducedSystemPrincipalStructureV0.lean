import ToeFormal.Derivation.QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticFullReducedSystemPrincipalStructureV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-FULL-REDUCED-SYSTEM-PRINCIPAL-STRUCTURE-v0"

def executionTarget : String :=
  "compute_qft_gr_quadratic_full_reduced_system_principal_structure_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_full_reduced_system_principal_structure_v0_result"

def variableOrder : List String :=
  ["g_mn", "c_mna", "R", "r_a", "S_mn"]

def componentDimensions : List Nat := [10, 40, 1, 4, 9]
def totalComponentCount : Nat := 64

def adaptedAuxiliaryWeights : List Nat := [2, 1, 2, 1, 1]
def metricEquivalenceWeights : List Nat := [3, 2, 1, 0, 1]

def adaptedRootAlgebraicMultiplicity : Nat := 64
def adaptedRootGeometricMultiplicity : Nat := 64
def metricRootAlgebraicMultiplicity : Nat := 64
def metricRootGeometricMultiplicity : Nat := 50

def metricJordanBlocksSizeThree : Nat := 4
def metricJordanBlocksSizeTwo : Nat := 6
def metricJordanBlocksSizeOne : Nat := 40

def fixedEquivalenceDerivativeLoss : Nat := 1
def adaptedAuxiliaryUniformDiagonalizerEstablished : Bool := true
def metricUniformDiagonalizerEstablished : Bool := false
def physicalSpinTwoDefectRepaired : Bool := false
def energyEstimateEstablished : Bool := false
def localExistenceEstablished : Bool := false

def acceptedTerminalOutcomes : List String :=
  [ "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_ONLY_IN_ADAPTED_GRADING",
    "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_DERIVATIVE_LOSS" ]

theorem reduced_variable_inventory_has_sixty_four_components :
    variableOrder.length = 5 ∧
      componentDimensions.sum = totalComponentCount := by
  decide

theorem adapted_and_metric_multiplicities_are_distinct :
    adaptedRootAlgebraicMultiplicity = 64 ∧
      adaptedRootGeometricMultiplicity = 64 ∧
      metricRootAlgebraicMultiplicity = 64 ∧
      metricRootGeometricMultiplicity = 50 ∧
      adaptedAuxiliaryUniformDiagonalizerEstablished = true ∧
      metricUniformDiagonalizerEstablished = false := by
  decide

theorem metric_root_jordan_partition_accounts_for_all_components :
    3 * metricJordanBlocksSizeThree +
          2 * metricJordanBlocksSizeTwo +
          metricJordanBlocksSizeOne =
        totalComponentCount ∧
      metricJordanBlocksSizeThree +
          metricJordanBlocksSizeTwo +
          metricJordanBlocksSizeOne =
        metricRootGeometricMultiplicity := by
  decide

theorem adapted_diagonalization_does_not_repair_metric_physics :
    fixedEquivalenceDerivativeLoss = 1 ∧
      physicalSpinTwoDefectRepaired = false ∧
      energyEstimateEstablished = false ∧
      localExistenceEstablished = false ∧
      acceptedTerminalOutcomes.length = 2 := by
  decide

end QFTGRQuadraticFullReducedSystemPrincipalStructureV0
end Derivation
end ToeFormal
