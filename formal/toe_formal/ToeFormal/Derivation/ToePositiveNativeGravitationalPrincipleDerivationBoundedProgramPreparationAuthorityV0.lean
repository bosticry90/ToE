namespace ToeFormal
namespace Derivation
namespace ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0

def authorityId : String :=
  "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0"

def authorizedTarget : String :=
  "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0"

def selectedRoute : String :=
  "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE"

def proposalPreparationAuthorized : Bool := true
def programInstalled : Bool := false
def scientificStageOpened : Bool := false
def principleInventoryExecuted : Bool := false
def nativeGravitationalPrincipleSelectedOrDerived : Bool := false
def gravitationalActionSelectedConstructedOrVaried : Bool := false
def gravitationalCalculationExecuted : Bool := false
def evidencePromoted : Bool := false
def scientificSuccessorAuthorized : Bool := false

theorem authority_is_exactly_preparation_only :
    authorizedTarget =
      "prepare_toe_positive_native_gravitational_principle_derivation_bounded_program_v0" ∧
    selectedRoute = "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE" ∧
    proposalPreparationAuthorized = true ∧
    programInstalled = false ∧ scientificStageOpened = false ∧
    principleInventoryExecuted = false ∧
    nativeGravitationalPrincipleSelectedOrDerived = false ∧
    gravitationalActionSelectedConstructedOrVaried = false ∧
    gravitationalCalculationExecuted = false ∧ evidencePromoted = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end ToePositiveNativeGravitationalPrincipleDerivationBoundedProgramPreparationAuthorityV0
end Derivation
end ToeFormal
