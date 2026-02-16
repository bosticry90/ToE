/-
ToeFormal/Variational/GR01AssumptionLedger.lean

Canonical assumption bundle and classification map for GR01 hardening work.

Scope:
- Bounded/discrete weak-field v0 only.
- No continuum-limit promotion.
- No Einstein-field-equation recovery claim.
- No comparator-lane expansion semantics.
-/

import Mathlib
import ToeFormal.Variational.GR01EndToEndClosure

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

inductive GR01AssumptionClass_v0 where
  | MATH
  | DEF
  | POLICY
  | SCOPE
  deriving DecidableEq, Repr

inductive GR01AssumptionTag_v0 where
  | epsilonNonzero
  | actionDefaultBinding
  | racRep32Cubic
  | pRep32DefaultBinding
  | potentialIdentification
  | sourceIdentification
  | laplacianExtraction
  | unitsAndCalibration
  | projectionCarrierWitness
  | weakFieldUniformBound
  | phiBoundWithinRegime
  | rhoBoundWithinRegime
  | phiScaleDominates
  | rhoScaleDominates
  | higherOrderTermsNegligible
  | firstOrderRemainderSuppressedDirect
  | remainderScaleZero
  | potentialCarrierEq
  | sourceCarrierEq
  | elImpliesOperatorResidualUnderBound
  deriving DecidableEq, Repr

def gr01AssumptionClass_v0 : GR01AssumptionTag_v0 → GR01AssumptionClass_v0
  | .epsilonNonzero => .SCOPE
  | .actionDefaultBinding => .MATH
  | .racRep32Cubic => .POLICY
  | .pRep32DefaultBinding => .MATH
  | .potentialIdentification => .DEF
  | .sourceIdentification => .DEF
  | .laplacianExtraction => .DEF
  | .unitsAndCalibration => .DEF
  | .projectionCarrierWitness => .DEF
  | .weakFieldUniformBound => .SCOPE
  | .phiBoundWithinRegime => .SCOPE
  | .rhoBoundWithinRegime => .SCOPE
  | .phiScaleDominates => .SCOPE
  | .rhoScaleDominates => .SCOPE
  | .higherOrderTermsNegligible => .MATH
  | .firstOrderRemainderSuppressedDirect => .MATH
  | .remainderScaleZero => .SCOPE
  | .potentialCarrierEq => .DEF
  | .sourceCarrierEq => .DEF
  | .elImpliesOperatorResidualUnderBound => .POLICY

structure GR01Assumptions_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness) where
  ε : Real
  hε : ε ≠ 0
  hAction : actionRep32.action = actionRep32Cubic declared_g_rep32
  hRAC : RACRep32CubicObligationSet declared_g_rep32
  hP : P_rep32 = P_cubic_rep32_def declared_g_rep32
  phiBound : Real
  rhoBound : Real
  regimeBound : Real
  phiScale : Real
  rhoScale : Real
  remainderScale : Real
  hWeakFieldUniformBound :
    WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound
  hPhiBoundWithin : phiBound ≤ regimeBound
  hRhoBoundWithin : rhoBound ≤ regimeBound
  hPhiScaleDominates : regimeBound ≤ phiScale * |ε|
  hRhoScaleDominates : regimeBound ≤ rhoScale * |ε|
  hHigherOrderTermsNegligible :
    HigherOrderTermsNegligible
      hPotentialIdentification
      hLaplacianExtraction
      ε
      remainderScale
  hRemainderScaleZero : remainderScale = 0
  hPotentialCarrierEq :
    hPotentialIdentification.Φ = carrierWitness.potentialCarrier
  hSourceCarrierEq :
    hSourceIdentification.ρ = carrierWitness.sourceCarrier
  hELImpliesOperatorResidualUnderBound :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound

theorem gr01_end_to_end_poisson_equation_of_GR01Assumptions_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (hAsm :
      GR01Assumptions_v0
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        carrierWitness) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  exact
    gr01_end_to_end_poisson_equation_under_promoted_assumptions_of_hP
      hAsm.ε
      hAsm.hε
      hAsm.hAction
      hAsm.hRAC
      hAsm.hP
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      carrierWitness
      hAsm.phiBound
      hAsm.rhoBound
      hAsm.regimeBound
      hAsm.phiScale
      hAsm.rhoScale
      hAsm.remainderScale
      hAsm.hPotentialCarrierEq
      hAsm.hSourceCarrierEq
      hAsm.hWeakFieldUniformBound
      hAsm.hPhiBoundWithin
      hAsm.hRhoBoundWithin
      hAsm.hPhiScaleDominates
      hAsm.hRhoScaleDominates
      hAsm.hHigherOrderTermsNegligible
      hAsm.hRemainderScaleZero
      hAsm.hELImpliesOperatorResidualUnderBound

structure GR01Assumptions_v0_min1
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness) where
  ε : Real
  hε : ε ≠ 0
  hAction : actionRep32.action = actionRep32Cubic declared_g_rep32
  hRAC : RACRep32CubicObligationSet declared_g_rep32
  phiBound : Real
  rhoBound : Real
  regimeBound : Real
  phiScale : Real
  rhoScale : Real
  remainderScale : Real
  hWeakFieldUniformBound :
    WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound
  hPhiBoundWithin : phiBound ≤ regimeBound
  hRhoBoundWithin : rhoBound ≤ regimeBound
  hPhiScaleDominates : regimeBound ≤ phiScale * |ε|
  hRhoScaleDominates : regimeBound ≤ rhoScale * |ε|
  hHigherOrderTermsNegligible :
    HigherOrderTermsNegligible
      hPotentialIdentification
      hLaplacianExtraction
      ε
      remainderScale
  hRemainderScaleZero : remainderScale = 0
  hPotentialCarrierEq :
    hPotentialIdentification.Φ = carrierWitness.potentialCarrier
  hSourceCarrierEq :
    hSourceIdentification.ρ = carrierWitness.sourceCarrier
  hELImpliesOperatorResidualUnderBound :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound

theorem gr01_end_to_end_poisson_equation_of_GR01Assumptions_v0_min1
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (carrierWitness : ProjectionCarrierWitness)
    (hAsm :
      GR01Assumptions_v0_min1
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        carrierWitness) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  exact
    gr01_end_to_end_poisson_equation_under_promoted_assumptions
      hAsm.ε
      hAsm.hε
      hAsm.hAction
      hAsm.hRAC
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      carrierWitness
      hAsm.phiBound
      hAsm.rhoBound
      hAsm.regimeBound
      hAsm.phiScale
      hAsm.rhoScale
      hAsm.remainderScale
      hAsm.hPotentialCarrierEq
      hAsm.hSourceCarrierEq
      hAsm.hWeakFieldUniformBound
      hAsm.hPhiBoundWithin
      hAsm.hRhoBoundWithin
      hAsm.hPhiScaleDominates
      hAsm.hRhoScaleDominates
      hAsm.hHigherOrderTermsNegligible
      hAsm.hRemainderScaleZero
      hAsm.hELImpliesOperatorResidualUnderBound

structure GR01Assumptions_v0_min2
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration) where
  ε : Real
  hε : ε ≠ 0
  hAction : actionRep32.action = actionRep32Cubic declared_g_rep32
  hRAC : RACRep32CubicObligationSet declared_g_rep32
  phiBound : Real
  rhoBound : Real
  hWeakFieldUniformBound :
    WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound
  hFirstOrderRemainderSuppressed :
    FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction
  hELImpliesOperatorResidualUnderBound :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound

theorem gr01_poisson_equation_of_GR01Assumptions_v0_min2
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hAsm :
      GR01Assumptions_v0_min2
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  intro i
  exact
    gr01_discrete_residual_from_bridge_promotion_chain
      hAsm.ε
      hAsm.hε
      hAsm.hAction
      hAsm.hRAC
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hAsm.phiBound
      hAsm.rhoBound
      hAsm.hWeakFieldUniformBound
      hAsm.hFirstOrderRemainderSuppressed
      hAsm.hELImpliesOperatorResidualUnderBound
      i

structure GR01Assumptions_v0_min3
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration) where
  ε : Real
  hε : ε ≠ 0
  hRAC : RACRep32CubicObligationSet declared_g_rep32
  phiBound : Real
  rhoBound : Real
  hWeakFieldUniformBound :
    WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound
  hFirstOrderRemainderSuppressed :
    FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction
  hELImpliesOperatorResidualUnderBound :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound

theorem gr01_poisson_equation_of_GR01Assumptions_v0_min3
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hAsm :
      GR01Assumptions_v0_min3
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    PoissonEquation1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  intro i
  exact
    gr01_discrete_residual_from_bridge_promotion_chain_default_binding
      hAsm.ε
      hAsm.hε
      hAsm.hRAC
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hAsm.phiBound
      hAsm.rhoBound
      hAsm.hWeakFieldUniformBound
      hAsm.hFirstOrderRemainderSuppressed
      hAsm.hELImpliesOperatorResidualUnderBound
      i

end
end Variational
end ToeFormal
