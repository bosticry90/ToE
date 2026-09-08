import ToeFormal.Derivation.QFTGRQuadraticAuxiliaryHarmonicAdaptedNormWellPosednessPacketResultReviewV0

namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticAuxiliaryHarmonicReducedSystemV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0"

def executionTarget : String :=
  "derive_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"

def resultReviewTarget : String :=
  "review_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0_result"

def unknownVector : List String :=
  ["g_mn", "R", "r_a", "c_mna", "S_mn"]

def evolutionEquations : List String :=
  ["E_g^H", "E_R", "E_r", "E_c", "E_S"]

def constraintIds : List String :=
  [ "C_H^a",
    "C_r_a",
    "C_c_mna",
    "C_R",
    "C_S_mn",
    "C_trace",
    "C_div_n",
    "C_curl_r_ab",
    "C_curl_c_mnab",
    "C_Hamiltonian",
    "C_momentum_a" ]

def traceAlphaBoxCoefficient : Int := 6
def traceBetaBoxCoefficient : Int := 2
def traceFreeTensorBoxUsesBeta : Bool := true
def kineticMapRequiresBetaNonzero : Bool := true
def kineticMapRequiresThreeAlphaPlusBetaNonzero : Bool := true

def exactReducedEquationsDerived : Bool := true
def algebraicEquivalenceOnFullConstraintSurfaceDerived : Bool := true
def arbitraryAuxiliarySolutionImpliesMetricSolution : Bool := false
def constraintPropagationEstablished : Bool := false
def energyEstimateEstablished : Bool := false
def localWellPosednessEstablished : Bool := false
def ordinaryMetricStrongHyperbolicityRestored : Bool := false

theorem five_field_second_order_system_is_exactly_bounded :
    unknownVector.length = 5 ∧
      evolutionEquations.length = 5 ∧
      constraintIds.length = 11 ∧
      traceAlphaBoxCoefficient = 6 ∧
      traceBetaBoxCoefficient = 2 ∧
      traceFreeTensorBoxUsesBeta = true ∧
      kineticMapRequiresBetaNonzero = true ∧
      kineticMapRequiresThreeAlphaPlusBetaNonzero = true := by
  decide

theorem reduced_system_does_not_promote_a_well_posedness_claim :
    exactReducedEquationsDerived = true ∧
      algebraicEquivalenceOnFullConstraintSurfaceDerived = true ∧
      arbitraryAuxiliarySolutionImpliesMetricSolution = false ∧
      constraintPropagationEstablished = false ∧
      energyEstimateEstablished = false ∧
      localWellPosednessEstablished = false ∧
      ordinaryMetricStrongHyperbolicityRestored = false := by
  decide

end QFTGRQuadraticAuxiliaryHarmonicReducedSystemV0
end Derivation
end ToeFormal
