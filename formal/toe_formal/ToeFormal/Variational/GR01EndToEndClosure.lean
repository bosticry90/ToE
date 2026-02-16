/-
ToeFormal/Variational/GR01EndToEndClosure.lean

End-to-end chain-composition theorem surface for GR01 closure work.

Scope:
- Contract-level theorem-chain composition for GR01 derivation-grade closure criteria.
- No external truth claim.
- No Einstein-field-equation recovery claim.
- No comparator-lane expansion semantics.
- Non-vacuous theorem signatures only.
-/

import Mathlib
import ToeFormal.Variational.GR01SymmetryPromotion
import ToeFormal.Variational.GR01ScalingPromotion

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

def GR01EndToEndClosureBundle
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (regimeBound ε phiScale rhoScale : Real) : Prop :=
  ProjectionMapWellFormed hPotentialIdentification hSourceIdentification ∧
    WeakFieldScalingHierarchy
      hPotentialIdentification
      hSourceIdentification
      ε
      phiScale
      rhoScale ∧
      (∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0)

theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier)
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
        rhoBound) :
    GR01EndToEndClosureBundle
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      regimeBound
      ε
      phiScale
      rhoScale := by
  have hRegimePredicate :
      WeakFieldRegimePredicate hPotentialIdentification hSourceIdentification regimeBound :=
    gr01_regime_predicate_under_uniform_bound
      hPotentialIdentification
      hSourceIdentification
      phiBound
      rhoBound
      regimeBound
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
  have hProjectionMapWellFormedPredicate :
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
      hProjectionMapWellFormedPredicate
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
  have hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction :=
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
      hFirstOrderRemainderSuppressed
      hELImpliesOperatorResidualUnderBound
  exact ⟨hProjectionMapWellFormed, hScalingHierarchy, hDiscreteResidual⟩

theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier)
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
        rhoBound) :
    GR01EndToEndClosureBundle
      hPotentialIdentification
      hSourceIdentification
      hUnitsAndCalibration
      regimeBound
      ε
      phiScale
      rhoScale := by
  exact
    gr01_end_to_end_chain_bundle_under_promoted_assumptions_of_hP
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
      regimeBound
      phiScale
      rhoScale
      remainderScale
      hPotentialCarrierEq
      hSourceCarrierEq
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
      hPhiScaleDominates
      hRhoScaleDominates
      hHigherOrderTermsNegligible
      hRemainderScaleZero
      hELImpliesOperatorResidualUnderBound

theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier)
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
        rhoBound) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  have hClosureBundle :
      GR01EndToEndClosureBundle
        hPotentialIdentification
        hSourceIdentification
      hUnitsAndCalibration
      regimeBound
      ε
      phiScale
      rhoScale :=
    gr01_end_to_end_chain_bundle_under_promoted_assumptions_of_hP
      ε
      hε
      hAction
      hRAC
      hP
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      carrierWitness
      phiBound
      rhoBound
      regimeBound
      phiScale
      rhoScale
      remainderScale
      hPotentialCarrierEq
      hSourceCarrierEq
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
      hPhiScaleDominates
      hRhoScaleDominates
      hHigherOrderTermsNegligible
      hRemainderScaleZero
      hELImpliesOperatorResidualUnderBound
  intro i
  exact hClosureBundle.2.2 i

theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)
    (hPotentialCarrierEq :
      hPotentialIdentification.Φ = carrierWitness.potentialCarrier)
    (hSourceCarrierEq :
      hSourceIdentification.ρ = carrierWitness.sourceCarrier)
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
        rhoBound) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  exact
    gr01_end_to_end_poisson_equation_under_promoted_assumptions_of_hP
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
      regimeBound
      phiScale
      rhoScale
      remainderScale
      hPotentialCarrierEq
      hSourceCarrierEq
      hWeakFieldUniformBound
      hPhiBoundWithin
      hRhoBoundWithin
      hPhiScaleDominates
      hRhoScaleDominates
      hHigherOrderTermsNegligible
      hRemainderScaleZero
      hELImpliesOperatorResidualUnderBound

end
end Variational
end ToeFormal
