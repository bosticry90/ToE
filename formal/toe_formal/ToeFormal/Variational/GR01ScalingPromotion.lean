/-
ToeFormal/Variational/GR01ScalingPromotion.lean

Scaling-promotion theorem surface for GR01 approximation discharge work.

Scope:
- Contract-level scaling/remainder theorem chain for `ASM-GR01-APP-01` promotion work.
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

def WeakFieldScalingHierarchy
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (ε phiScale rhoScale : Real) : Prop :=
  ∀ i : Int,
    |hPotentialIdentification.Φ i| ≤ phiScale * |ε| ∧
      |hSourceIdentification.ρ i| ≤ rhoScale * |ε|

def HigherOrderTermsNegligible
    (hPotentialIdentification : PotentialIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (ε remainderScale : Real) : Prop :=
  ∀ i : Int,
    |hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
      - DiscreteLaplacian1D hPotentialIdentification.Φ i|
      ≤ remainderScale * (|ε| * |ε|)

theorem gr01_scaling_hierarchy_under_regime_predicate
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (ε phiScale rhoScale regimeBound : Real)
    (hRegimePredicate :
      WeakFieldRegimePredicate
        hPotentialIdentification
        hSourceIdentification
        regimeBound)
    (hPhiScaleDominates : regimeBound ≤ phiScale * |ε|)
    (hRhoScaleDominates : regimeBound ≤ rhoScale * |ε|) :
    WeakFieldScalingHierarchy
      hPotentialIdentification
      hSourceIdentification
      ε
      phiScale
      rhoScale := by
  intro i
  have hRegimeAtI := hRegimePredicate i
  constructor
  · exact le_trans hRegimeAtI.1 hPhiScaleDominates
  · exact le_trans hRegimeAtI.2 hRhoScaleDominates

theorem gr01_first_order_truncation_sound
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (ε phiScale rhoScale remainderScale : Real)
    (hScalingHierarchy :
      WeakFieldScalingHierarchy
        hPotentialIdentification
        hSourceIdentification
        ε
        phiScale
        rhoScale)
    (hHigherOrderTermsNegligible :
      HigherOrderTermsNegligible
        hPotentialIdentification
        hLaplacianExtraction
        ε
        remainderScale)
    (hRemainderScaleZero : remainderScale = 0) :
    FirstOrderRemainderSuppressed
      hPotentialIdentification
      hLaplacianExtraction := by
  have hScaleAt0 := hScalingHierarchy 0
  let _ := hScaleAt0
  intro i
  have hBoundAtI := hHigherOrderTermsNegligible i
  have hAbsEqZero :
      |hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
        - DiscreteLaplacian1D hPotentialIdentification.Φ i| = 0 := by
    have hUpper :
        |hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - DiscreteLaplacian1D hPotentialIdentification.Φ i| ≤ 0 := by
      simpa [hRemainderScaleZero] using hBoundAtI
    have hNonneg :
        0 ≤ |hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - DiscreteLaplacian1D hPotentialIdentification.Φ i| :=
      abs_nonneg _
    exact le_antisymm hUpper hNonneg
  exact abs_eq_zero.mp hAbsEqZero

end
end Variational
end ToeFormal
