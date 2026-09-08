namespace ToeFormal
namespace Derivation
namespace QFTGRQuadraticPhysicalSpin2PrincipalBlockV0

def calculationId : String :=
  "CALC-QFT-GR-QUADRATIC-PHYSICAL-SPIN2-PRINCIPAL-BLOCK-v0"

def executionTarget : String :=
  "derive_qft_gr_quadratic_physical_spin2_principal_block_v0"

def selectedNextTarget : String :=
  "review_qft_gr_quadratic_physical_spin2_principal_block_v0_result"

def physicalPencilScalar (beta lambda : Int) : Int :=
  -beta * (lambda * lambda - 1) ^ 2

def algebraicMultiplicityAtLightCone : Nat := 4
def geometricMultiplicityAtLightCone : Nat := 2
def allCharacteristicRootsReal : Bool := true
def completeEigenbasis : Bool := false
def stronglyHyperbolic : Bool := false
def symmetricallyHyperbolic : Bool := false
def adaptedNormLocalWellPosednessEstablished : Bool := false

theorem light_cone_roots_vanish (beta : Int) :
    physicalPencilScalar beta 1 = 0 ∧
      physicalPencilScalar beta (-1) = 0 := by
  simp [physicalPencilScalar]

theorem repeated_roots_are_defective :
    algebraicMultiplicityAtLightCone >
      geometricMultiplicityAtLightCone := by
  decide

theorem beta_zero_removes_quartic_spin2_block (lambda : Int) :
    physicalPencilScalar 0 lambda = 0 := by
  simp [physicalPencilScalar]

theorem reviewed_claim_boundary :
    allCharacteristicRootsReal = true ∧
      completeEigenbasis = false ∧
      stronglyHyperbolic = false ∧
      symmetricallyHyperbolic = false ∧
      adaptedNormLocalWellPosednessEstablished = false := by
  decide

end QFTGRQuadraticPhysicalSpin2PrincipalBlockV0
end Derivation
end ToeFormal
