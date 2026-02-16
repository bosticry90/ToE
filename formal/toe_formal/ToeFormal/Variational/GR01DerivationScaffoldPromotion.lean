/-
ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean

DER-01 scaffold-promotion theorem surface for GR01 weak-field derivation work.

Scope:
- Contract-level scaffold bundle for weak-field expansion, potential/source identification,
  Laplacian extraction, and projection-map well-formedness.
- No external truth claim.
- No Einstein-field-equation recovery claim.
- No comparator-lane expansion semantics.
-/

import Mathlib
import ToeFormal.Variational.GR01BridgePromotion
import ToeFormal.Variational.GR01ScalingPromotion
import ToeFormal.Variational.GR01SymmetryPromotion

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

structure GR01DerivationScaffoldBundle
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (ε phiScale rhoScale regimeBound : Real) : Prop where
  regime_predicate :
    WeakFieldRegimePredicate hPotentialIdentification hSourceIdentification regimeBound
  scaling_hierarchy :
    WeakFieldScalingHierarchy
      hPotentialIdentification
      hSourceIdentification
      ε
      phiScale
      rhoScale
  first_order_truncation :
    FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction
  projection_map_well_formed :
    ProjectionMapWellFormed hPotentialIdentification hSourceIdentification
  discrete_residual_zero :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0

theorem gr01_der01_scaffold_bundle_under_promoted_assumptions_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound : Real)
    (phiScale rhoScale : Real)
    (regimeBound : Real)
    (remainderScale : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hPhiBoundWithin : phiBound ≤ regimeBound)
    (hRhoBoundWithin : rhoBound ≤ regimeBound)
    (hPhiScaleDominates : regimeBound ≤ phiScale * |ε|)
    (hRhoScaleDominates : regimeBound ≤ rhoScale * |ε|)
    (hHigherOrderTermsNegligible :
      HigherOrderTermsNegligible
        hPotentialIdentification
        hLaplacianExtraction
        ε
        remainderScale)
    (hRemainderScaleZero : remainderScale = 0)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier) :
    GR01DerivationScaffoldBundle
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      ε
      phiScale
      rhoScale
      regimeBound := by
  have hRegimePredicate :
      WeakFieldRegimePredicate
        hPotentialIdentification
        hSourceIdentification
        regimeBound :=
    gr01_regime_predicate_under_uniform_bound
      hPotentialIdentification
      hSourceIdentification
      phiBound
      rhoBound
      regimeBound
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
  have hScalingHierarchy :
      WeakFieldScalingHierarchy
        hPotentialIdentification
        hSourceIdentification
        ε
        phiScale
        rhoScale :=
    gr01_scaling_hierarchy_under_regime_predicate
      hPotentialIdentification
      hSourceIdentification
      ε
      phiScale
      rhoScale
      regimeBound
      hRegimePredicate
      hPhiScaleDominates
      hRhoScaleDominates
  have hFirstOrderTruncation :
      FirstOrderRemainderSuppressed
        hPotentialIdentification
        hLaplacianExtraction :=
    gr01_first_order_truncation_sound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      ε
      phiScale
      rhoScale
      remainderScale
      hScalingHierarchy
      hHigherOrderTermsNegligible
      hRemainderScaleZero
  have hProjectionPredicate :
      ProjectionMapWellFormedPredicate
        hPotentialIdentification
        hSourceIdentification
        carrierWitness
        regimeBound :=
    gr01_projection_map_well_formed_under_regime_predicate
      hPotentialIdentification
      hSourceIdentification
      carrierWitness
      regimeBound
      hPotentialCarrierEq
      hSourceCarrierEq
      hRegimePredicate
  have hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification :=
    gr01_projection_map_well_formed
      hPotentialIdentification
      hSourceIdentification
      carrierWitness
      regimeBound
      hProjectionPredicate
  have hDiscreteResidual :
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    gr01_discrete_residual_from_bridge_promotion_chain_of_hP
      ε
      hε
      hAction
      hRAC
      hP
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hFirstOrderTruncation
      hELImpliesOperatorResidualUnderBound
  exact
    {
      regime_predicate := hRegimePredicate
      scaling_hierarchy := hScalingHierarchy
      first_order_truncation := hFirstOrderTruncation
      projection_map_well_formed := hProjectionMapWellFormed
      discrete_residual_zero := hDiscreteResidual
    }

theorem gr01_der01_scaffold_bundle_under_promoted_assumptions
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound : Real)
    (phiScale rhoScale : Real)
    (regimeBound : Real)
    (remainderScale : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hPhiBoundWithin : phiBound ≤ regimeBound)
    (hRhoBoundWithin : rhoBound ≤ regimeBound)
    (hPhiScaleDominates : regimeBound ≤ phiScale * |ε|)
    (hRhoScaleDominates : regimeBound ≤ rhoScale * |ε|)
    (hHigherOrderTermsNegligible :
      HigherOrderTermsNegligible
        hPotentialIdentification
        hLaplacianExtraction
        ε
        remainderScale)
    (hRemainderScaleZero : remainderScale = 0)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier) :
    GR01DerivationScaffoldBundle
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      ε
      phiScale
      rhoScale
      regimeBound := by
  exact
    gr01_der01_scaffold_bundle_under_promoted_assumptions_of_hP
      ε
      hε
      hAction
      hRAC
      P_rep32_def
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      carrierWitness
      phiBound
      rhoBound
      phiScale
      rhoScale
      regimeBound
      remainderScale
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
      hPhiScaleDominates
      hRhoScaleDominates
      hHigherOrderTermsNegligible
      hRemainderScaleZero
      hELImpliesOperatorResidualUnderBound
      hPotentialCarrierEq
      hSourceCarrierEq

end
end Variational
end ToeFormal
