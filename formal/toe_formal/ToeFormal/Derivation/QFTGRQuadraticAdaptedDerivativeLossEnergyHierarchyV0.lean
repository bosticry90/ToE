import ToeFormal.Derivation.QFTGRQuadraticFullReducedSystemPrincipalStructureResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticAdaptedDerivativeLossEnergyHierarchyV0

def packetId : String :=
  "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_HIERARCHY_20260728_v0"

def preparationTarget : String :=
  "prepare_qft_gr_quadratic_adapted_derivative_loss_energy_hierarchy_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_adapted_derivative_loss_energy_hierarchy_v0_result"

def adaptedAuxiliaryWeights : List Int := [2, 1, 2, 1, 1]
def metricEquivalenceWeights : List Int := [3, 2, 1, 0, 1]

def lengthThreeChainCount : Nat := 4
def lengthTwoChainCount : Nat := 6
def lengthOneChainCount : Nat := 40
def chainCountAtEachRoot : Nat := 50
def algebraicDimensionAtEachRoot : Nat := 64
def eigenvectorDeficitAtEachRoot : Nat := 14
def physicalTTDeficitAtEachRoot : Nat := 2
def reconstructionDeficitAtEachRoot : Nat := 8
def nonTTLengthTwoDeficitAtEachRoot : Nat := 4

def provedEquivalenceMapDerivativeShift : Nat := 1
def propagatorLossOneDerivativeEstablished : Bool := false
def propagatorLossTwoDerivativesRefuted : Bool := false
def energyEstimateEstablished : Bool := false
def lossNonaccumulationEstablished : Bool := false
def localExistenceEstablished : Bool := false

def proofLevels : List String :=
  [ "FROZEN_COEFFICIENT_FOURIER_PROPAGATOR",
    "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
    "QUASILINEAR_TAME_ESTIMATE",
    "ITERATION_CLOSURE" ]

def preparationOutcomes : List String :=
  [ "ADAPTED_ENERGY_HIERARCHY_READY",
    "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
    "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_NOT_YET_ESTIMATED" ]

theorem jordan_chain_partition_closes :
    lengthThreeChainCount + lengthTwoChainCount + lengthOneChainCount =
        chainCountAtEachRoot ∧
      3 * lengthThreeChainCount +
          2 * lengthTwoChainCount +
          lengthOneChainCount =
        algebraicDimensionAtEachRoot := by
  decide

theorem eigenvector_deficit_is_completely_partitioned :
    physicalTTDeficitAtEachRoot +
          reconstructionDeficitAtEachRoot +
          nonTTLengthTwoDeficitAtEachRoot =
        eigenvectorDeficitAtEachRoot := by
  decide

theorem equivalence_shift_is_not_a_propagator_theorem :
    provedEquivalenceMapDerivativeShift = 1 ∧
      propagatorLossOneDerivativeEstablished = false ∧
      propagatorLossTwoDerivativesRefuted = false ∧
      energyEstimateEstablished = false ∧
      lossNonaccumulationEstablished = false ∧
      localExistenceEstablished = false := by
  decide

theorem preparation_freezes_four_proof_levels :
    proofLevels.length = 4 ∧
      preparationOutcomes.length = 3 := by
  decide

end QFTGRQuadraticAdaptedDerivativeLossEnergyHierarchyV0
end Derivation
end ToeFormal
