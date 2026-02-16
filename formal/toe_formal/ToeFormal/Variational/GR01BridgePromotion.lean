/-
ToeFormal/Variational/GR01BridgePromotion.lean

Bridge-promotion theorem surface for GR01 blocker discharge work.

Scope:
- Contract-level bridge lemma chain for `ASM-GR01-APP-02` promotion work.
- No external truth claim.
- No Einstein-field-equation recovery claim.
- No comparator-lane expansion semantics.
- Non-vacuous theorem signatures only.
-/

import Mathlib
import ToeFormal.Variational.WeakFieldPoissonLimit

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

def WeakFieldUniformBound
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (phiBound rhoBound : Real) : Prop :=
  ∀ i : Int,
    |hPotentialIdentification.Φ i| ≤ phiBound ∧
      |hSourceIdentification.ρ i| ≤ rhoBound

def WeakFieldRegimePredicate
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (regimeBound : Real) : Prop :=
  ∀ i : Int,
    |hPotentialIdentification.Φ i| ≤ regimeBound ∧
      |hSourceIdentification.ρ i| ≤ regimeBound

def FirstOrderRemainderSuppressed
    (hPotentialIdentification : PotentialIdentification)
    (hLaplacianExtraction : LaplacianExtraction) : Prop :=
  ∀ i : Int,
    hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
      - DiscreteLaplacian1D hPotentialIdentification.Φ i = 0

def ELImpliesOperatorResidualUnderBound
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real) : Prop :=
  WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound →
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 →
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0

def ELImpliesOperatorResidualTransport
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration) : Prop :=
  EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 →
    ∀ i : Int,
      hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
        - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0

theorem gr01_operator_residual_under_bound_from_transport
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    ELImpliesOperatorResidualUnderBound
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound := by
  intro _hWeakFieldUniformBound hELCore i
  exact hTransport hELCore i

theorem gr01_extraction_agrees_with_suppressed_remainder
    (hPotentialIdentification : PotentialIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction) :
    ∀ i : Int,
      hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
        = DiscreteLaplacian1D hPotentialIdentification.Φ i := by
  intro i
  have hAtI := hFirstOrderRemainderSuppressed i
  linarith

theorem gr01_regime_predicate_under_uniform_bound
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (phiBound rhoBound regimeBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hPhiBoundWithin : phiBound ≤ regimeBound)
    (hRhoBoundWithin : rhoBound ≤ regimeBound) :
    WeakFieldRegimePredicate hPotentialIdentification hSourceIdentification regimeBound := by
  intro i
  have hBoundAtI := hWeakFieldUniformBound i
  constructor
  · exact le_trans hBoundAtI.1 hPhiBoundWithin
  · exact le_trans hBoundAtI.2 hRhoBoundWithin

theorem gr01_projection_map_well_formed_from_uniform_bound_v0
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound) :
    ProjectionMapWellFormed hPotentialIdentification hSourceIdentification := by
  refine {
    potential_carrier_defined := ?_,
    source_carrier_defined := ?_,
    weak_field_regime_exists := ?_
  }
  · exact ⟨hPotentialIdentification.Φ, rfl⟩
  · exact ⟨hSourceIdentification.ρ, rfl⟩
  · refine ⟨max phiBound rhoBound, ?_⟩
    intro i
    have hBoundAtI := hWeakFieldUniformBound i
    constructor
    · exact le_trans hBoundAtI.1 (le_max_left phiBound rhoBound)
    · exact le_trans hBoundAtI.2 (le_max_right phiBound rhoBound)

theorem gr01_operator_residual_from_bound_bridge_assumptions
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound)
    (hELCore : EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32) :
    ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
        - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0 :=
  hELImpliesOperatorResidualUnderBound hWeakFieldUniformBound hELCore

theorem gr01_operator_residual_transport_from_bound_bridge_assumptions
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ELImpliesOperatorResidualTransport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  intro hELCore i
  exact
    gr01_operator_residual_from_bound_bridge_assumptions
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
      hELCore
      i

theorem gr01_el_implies_discrete_poisson_residual_from_bridge_promotion
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ELImpliesDiscretePoissonResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  refine ⟨?_⟩
  intro hELCore i
  have hResidualFromCore :
      ∀ j : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ j
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ j = 0 :=
    gr01_operator_residual_from_bound_bridge_assumptions
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
      hELCore
  exact
    OperatorToDiscreteResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hResidualFromCore
      i

theorem gr01_el_implies_discrete_poisson_residual_from_operator_transport
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    ELImpliesDiscretePoissonResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  refine ⟨?_⟩
  intro hELCore i
  have hResidualFromCore :
      ∀ j : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ j
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ j = 0 :=
    hOperatorTransport hELCore
  exact
    OperatorToDiscreteResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hResidualFromCore
      i

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    gr01_el_implies_discrete_poisson_residual_from_operator_transport
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hOperatorTransport
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := hAction
  let _ := hRAC
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hOperatorTransport

theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_derived_from_operator_transport_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hOperatorTransport :
      ELImpliesOperatorResidualTransport
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := hRAC
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hOperatorTransport

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_minimal_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    WeakFieldPoissonLimitStatement := by
  have hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    gr01_el_implies_discrete_poisson_residual_from_bridge_promotion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := hAction
  let _ := hRAC
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound

theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_derived_from_bridge_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed
        hPotentialIdentification
        hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    WeakFieldPoissonLimitStatement := by
  let _ := hRAC
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_minimal_of_hP
      ε
      hε
      hP
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound

theorem gr01_discrete_residual_from_bridge_promotion_chain_minimal_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  let _ := ε
  let _ := hε
  have hELCore :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
    simpa [hP] using EL_toe_eq_P_rep32
  have hResidualFromCore :
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0 :=
    gr01_operator_residual_from_bound_bridge_assumptions
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hELImpliesOperatorResidualUnderBound
      hELCore
  have hExtractionAgreement :
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          = DiscreteLaplacian1D hPotentialIdentification.Φ i :=
    gr01_extraction_agrees_with_suppressed_remainder
      hPotentialIdentification
      hLaplacianExtraction
      hFirstOrderRemainderSuppressed
  have hExtractionAgreement0 :
      hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ 0
        = DiscreteLaplacian1D hPotentialIdentification.Φ 0 :=
    hExtractionAgreement 0
  let _ := hExtractionAgreement0
  exact
    OperatorToDiscreteResidual
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hResidualFromCore

theorem gr01_discrete_residual_from_bridge_promotion_chain_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  let _ := hAction
  let _ := hRAC
  exact
    gr01_discrete_residual_from_bridge_promotion_chain_minimal_of_hP
      ε
      hε
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

theorem gr01_discrete_residual_from_bridge_promotion_chain_default_binding_of_hP
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hP : P_rep32 = P_cubic_rep32_def declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  let _ := hRAC
  exact
    gr01_discrete_residual_from_bridge_promotion_chain_minimal_of_hP
      ε
      hε
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

theorem gr01_discrete_residual_from_bridge_promotion_chain
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  exact
    gr01_discrete_residual_from_bridge_promotion_chain_of_hP
      ε
      hε
      hAction
      hRAC
      P_rep32_def
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hFirstOrderRemainderSuppressed
      hELImpliesOperatorResidualUnderBound

theorem gr01_discrete_residual_from_bridge_promotion_chain_default_binding
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      WeakFieldUniformBound hPotentialIdentification hSourceIdentification phiBound rhoBound)
    (hFirstOrderRemainderSuppressed :
      FirstOrderRemainderSuppressed hPotentialIdentification hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  exact
    gr01_discrete_residual_from_bridge_promotion_chain_default_binding_of_hP
      ε
      hε
      hRAC
      P_rep32_def
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hFirstOrderRemainderSuppressed
      hELImpliesOperatorResidualUnderBound

end
end Variational
end ToeFormal
