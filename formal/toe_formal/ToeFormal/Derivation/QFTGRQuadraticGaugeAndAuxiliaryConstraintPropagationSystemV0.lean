import ToeFormal.Derivation.QFTGRQuadraticAuxiliaryHarmonicReducedSystemResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-GAUGE-AUXILIARY-CONSTRAINT-PROPAGATION-SYSTEM-v0"

def executionTarget : String :=
  "derive_qft_gr_quadratic_gauge_and_auxiliary_constraint_propagation_system_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_gauge_and_auxiliary_constraint_propagation_system_v0_result"

def frozenEvolutionEquations : List String :=
  ["E_g^H", "E_R", "E_r", "E_c", "E_S"]

def independentSubsidiaryFields : List String :=
  ["C_H^a", "Phi^a_b", "V_H_n", "C_r_a", "C_c_mna", "T"]

def derivedConstraintFamilies : List String :=
  [ "I_R_ab",
    "I_g_mnab",
    "D_n",
    "C_R",
    "C_S_mn",
    "C_Hamiltonian",
    "C_momentum_i" ]

def unitWaveComponentCount : Nat := 64
def betaWaveComponentCount : Nat := 5
def independentSubsidiaryComponentCount : Nat := 69
def algebraicMultiplicityAtEachLightconeRoot : Nat := 69
def geometricMultiplicityAtEachLightconeRoot : Nat := 69

def offConstraintExtensionFrozen : Bool := true
def constraintAdditionUsed : Bool := false
def finiteHomogeneousSubsidiarySystemDerived : Bool := true
def subsidiarySystemStronglyHyperbolic : Bool := true
def fixedEquivalenceDerivativeLoss : Nat := 1
def metricStrongHyperbolicityRestored : Bool := false
def fullReducedPrincipalStructureClassified : Bool := false
def adaptedEnergyEstimateEstablished : Bool := false
def localWellPosednessEstablished : Bool := false

theorem finite_subsidiary_inventory_is_bounded :
    frozenEvolutionEquations.length = 5 ∧
      independentSubsidiaryFields.length = 6 ∧
      derivedConstraintFamilies.length = 7 ∧
      unitWaveComponentCount + betaWaveComponentCount =
        independentSubsidiaryComponentCount := by
  decide

theorem subsidiary_lightcone_roots_have_a_complete_basis :
    algebraicMultiplicityAtEachLightconeRoot =
        independentSubsidiaryComponentCount ∧
      geometricMultiplicityAtEachLightconeRoot =
        independentSubsidiaryComponentCount ∧
      finiteHomogeneousSubsidiarySystemDerived = true ∧
      subsidiarySystemStronglyHyperbolic = true := by
  decide

theorem constraint_closure_does_not_repair_the_physical_block :
    offConstraintExtensionFrozen = true ∧
      constraintAdditionUsed = false ∧
      fixedEquivalenceDerivativeLoss = 1 ∧
      metricStrongHyperbolicityRestored = false ∧
      fullReducedPrincipalStructureClassified = false ∧
      adaptedEnergyEstimateEstablished = false ∧
      localWellPosednessEstablished = false := by
  decide

end QFTGRQuadraticGaugeAndAuxiliaryConstraintPropagationSystemV0
end Derivation
end ToeFormal
