/-
ToeFormal/Constraints/SeamWitnessPackages.lean

Typed witness-package surfaces for seam-constraint promotion.

Scope:
- structural witness packaging only
- no theorem promotion by itself
- no empirical adjudication by itself
- no external truth claim
-/

import Mathlib

namespace ToeFormal
namespace Constraints

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

structure SeamWitnessHeader where
  seamId : String
  sourceAssumptionIds : List String
  routeTag : String
  noPromotionTag : String

structure CompatibilitySeamWitness where
  header : SeamWitnessHeader
  interfaceContractTag : String
  localizationTag : String

structure BridgeAdmissibilitySeamWitness where
  header : SeamWitnessHeader
  variationSourceTag : String
  operatorTargetTag : String
  constructorWitnessTag : String

structure TransportConsistencySeamWitness where
  header : SeamWitnessHeader
  transportMapTag : String
  residualLawTag : String
  preservationTag : String

structure RegimeInterfaceBoundednessSeamWitness where
  header : SeamWitnessHeader
  regimeLimitTag : String
  boundednessWindowTag : String
  validityTransferTag : String

end

end Constraints
end ToeFormal
