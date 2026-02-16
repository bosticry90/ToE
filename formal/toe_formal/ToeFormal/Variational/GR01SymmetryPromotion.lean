/-
ToeFormal/Variational/GR01SymmetryPromotion.lean

Symmetry-promotion theorem surface for GR01 projection-map discharge work.

Scope:
- Contract-level projection/symmetry theorem chain for `ASM-GR01-SYM-01` promotion work.
- No external truth claim.
- No Einstein-field-equation recovery claim.
- No comparator-lane expansion semantics.
- Non-vacuous theorem signatures only.
-/

import Mathlib
import ToeFormal.Variational.GR01BridgePromotion

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

structure ProjectionCarrierWitness where
  potentialCarrier : ScalarField1D
  sourceCarrier : ScalarField1D

def ProjectionMapWellFormedPredicate
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (carrierWitness : ProjectionCarrierWitness)
    (regimeBound : Real) : Prop :=
  hPotentialIdentification.Φ = carrierWitness.potentialCarrier ∧
    hSourceIdentification.ρ = carrierWitness.sourceCarrier ∧
      WeakFieldRegimePredicate hPotentialIdentification hSourceIdentification regimeBound

theorem gr01_projection_map_well_formed_under_regime_predicate
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (carrierWitness : ProjectionCarrierWitness)
    (regimeBound : Real)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier)
    (hRegimePredicate :
      WeakFieldRegimePredicate hPotentialIdentification hSourceIdentification regimeBound) :
    ProjectionMapWellFormedPredicate
      hPotentialIdentification
      hSourceIdentification
      carrierWitness
      regimeBound := by
  exact ⟨hPotentialCarrierEq, hSourceCarrierEq, hRegimePredicate⟩

theorem gr01_projection_map_well_formed
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (carrierWitness : ProjectionCarrierWitness)
    (regimeBound : Real)
    (hProjectionMapWellFormedPredicate :
      ProjectionMapWellFormedPredicate
        hPotentialIdentification
        hSourceIdentification
        carrierWitness
        regimeBound) :
    ProjectionMapWellFormed hPotentialIdentification hSourceIdentification := by
  rcases hProjectionMapWellFormedPredicate with
    ⟨hPotentialCarrierEq, hSourceCarrierEq, hRegimePredicate⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨carrierWitness.potentialCarrier, hPotentialCarrierEq⟩
  · exact ⟨carrierWitness.sourceCarrier, hSourceCarrierEq⟩
  · exact ⟨regimeBound, hRegimePredicate⟩

end
end Variational
end ToeFormal
