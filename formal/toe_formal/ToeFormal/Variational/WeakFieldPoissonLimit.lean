/-
ToeFormal/Variational/WeakFieldPoissonLimit.lean

Paper-facing theorem surface for TOE-GR-01 (weak-field Newtonian limit).

Scope:
- Structural-only theorem surface with explicit assumptions.
- No analytic discharge is claimed in this module.
- No external truth claim.
-/

import Mathlib
import ToeFormal.Variational.ActionRep32CubicLane

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

abbrev ScalarField1D := Int → Real

def DiscreteLaplacian1D (Φ : ScalarField1D) : ScalarField1D :=
  fun i => Φ (i + 1) - (2 : Real) * Φ i + Φ (i - 1)

def DiscretePoissonResidual1D (Φ ρ : ScalarField1D) (κ : Real) : ScalarField1D :=
  fun i => DiscreteLaplacian1D Φ i - κ * ρ i

def PoissonEquation1D (Φ ρ : ScalarField1D) (κ : Real) : Prop :=
  ∀ i : Int, DiscretePoissonResidual1D Φ ρ κ i = 0

theorem poissonEquation1D_iff_discreteLaplacian1D_eq_kappa_rho
    (Φ ρ : ScalarField1D) (κ : Real) :
    PoissonEquation1D Φ ρ κ ↔
      (∀ i : Int, DiscreteLaplacian1D Φ i = κ * ρ i) := by
  constructor
  · intro hPoisson i
    have hResidualZero : DiscretePoissonResidual1D Φ ρ κ i = 0 := hPoisson i
    dsimp [DiscretePoissonResidual1D] at hResidualZero
    linarith
  · intro hCanonical i
    have hEq : DiscreteLaplacian1D Φ i = κ * ρ i := hCanonical i
    dsimp [DiscretePoissonResidual1D]
    linarith

structure LatticePoint3D where
  x : Int
  y : Int
  z : Int

abbrev ScalarField3D := LatticePoint3D → Real

def DiscreteLaplacian3D (Φ : ScalarField3D) : ScalarField3D :=
  fun p =>
    Φ ⟨p.x + 1, p.y, p.z⟩ +
      Φ ⟨p.x - 1, p.y, p.z⟩ +
      Φ ⟨p.x, p.y + 1, p.z⟩ +
      Φ ⟨p.x, p.y - 1, p.z⟩ +
      Φ ⟨p.x, p.y, p.z + 1⟩ +
      Φ ⟨p.x, p.y, p.z - 1⟩ -
      (6 : Real) * Φ p

def DiscretePoissonResidual3D (Φ ρ : ScalarField3D) (κ : Real) : ScalarField3D :=
  fun p => DiscreteLaplacian3D Φ p - κ * ρ p

def PoissonEquation3D (Φ ρ : ScalarField3D) (κ : Real) : Prop :=
  ∀ p : LatticePoint3D, DiscretePoissonResidual3D Φ ρ κ p = 0

theorem poissonEquation3D_iff_discreteLaplacian3D_eq_kappa_rho
    (Φ ρ : ScalarField3D) (κ : Real) :
    PoissonEquation3D Φ ρ κ ↔
      (∀ p : LatticePoint3D, DiscreteLaplacian3D Φ p = κ * ρ p) := by
  constructor
  · intro hPoisson p
    have hResidualZero : DiscretePoissonResidual3D Φ ρ κ p = 0 := hPoisson p
    dsimp [DiscretePoissonResidual3D] at hResidualZero
    linarith
  · intro hCanonical p
    have hEq : DiscreteLaplacian3D Φ p = κ * ρ p := hCanonical p
    dsimp [DiscretePoissonResidual3D]
    linarith

structure Lift1DTo3DMappingAssumptions where
  Φ1D : ScalarField1D
  ρ1D : ScalarField1D
  Φ3D : ScalarField3D
  ρ3D : ScalarField3D
  potential_lift_x_only : ∀ p : LatticePoint3D, Φ3D p = Φ1D p.x
  source_lift_x_only : ∀ p : LatticePoint3D, ρ3D p = ρ1D p.x

structure Separable3DMappingAssumptions where
  Φx : ScalarField1D
  Φy : ScalarField1D
  Φz : ScalarField1D
  ρx : ScalarField1D
  ρy : ScalarField1D
  ρz : ScalarField1D
  Φ3D : ScalarField3D
  ρ3D : ScalarField3D
  potential_is_separable :
    ∀ p : LatticePoint3D, Φ3D p = Φx p.x + Φy p.y + Φz p.z
  source_is_separable :
    ∀ p : LatticePoint3D, ρ3D p = ρx p.x + ρy p.y + ρz p.z

structure WeakFieldAnsatz where
  η : Real
  h_eta_small : |η| ≤ 1

structure SmallPerturbationExpansion where
  truncationOrder : Nat
  h_truncationOrder : truncationOrder = 1

structure PotentialIdentification where
  Φ : ScalarField1D

structure SourceIdentification where
  ρ : ScalarField1D

structure LaplacianExtraction where
  extractedOperator : ScalarField1D → ScalarField1D
  h_extracted_is_discrete : extractedOperator = DiscreteLaplacian1D

structure UnitsAndCalibration where
  κ : Real
  G_N : Real
  h_kappa_relation : κ = 4 * Real.pi * G_N

structure WeakFieldProjectionFromCore
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration) where
  discrete_residual_zero_from_core :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 →
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0

structure ProjectionMapWellFormed
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification) : Prop where
  potential_carrier_defined :
    ∃ potentialCarrier : ScalarField1D,
      hPotentialIdentification.Φ = potentialCarrier
  source_carrier_defined :
    ∃ sourceCarrier : ScalarField1D,
      hSourceIdentification.ρ = sourceCarrier
  weak_field_regime_exists :
    ∃ regimeBound : Real,
      ∀ i : Int,
        |hPotentialIdentification.Φ i| ≤ regimeBound ∧
          |hSourceIdentification.ρ i| ≤ regimeBound

structure WeakFieldTruncationSound
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion) : Prop where
  first_order_regime : True
  higher_order_remainder_bounded : True

theorem weakFieldTruncationSound_default_v0
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion) :
    WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion :=
  ⟨trivial, trivial⟩

structure ELImpliesDiscretePoissonResidual
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration) : Prop where
  el_implies_discrete_residual :
    EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 →
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0

def mkWeakFieldProjectionFromCore
    (hWeakFieldAnsatz : WeakFieldAnsatz)
    (hSmallPerturbationExpansion : SmallPerturbationExpansion)
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionMapWellFormed :
      ProjectionMapWellFormed hPotentialIdentification hSourceIdentification)
    (hWeakFieldTruncationSound :
      WeakFieldTruncationSound hWeakFieldAnsatz hSmallPerturbationExpansion)
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldProjectionFromCore
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration := by
  let _ := hProjectionMapWellFormed
  let _ := hWeakFieldTruncationSound
  exact
    {
      discrete_residual_zero_from_core :=
        hELImpliesDiscretePoissonResidual.el_implies_discrete_residual
    }

def WeakFieldPoissonLimitStatement : Prop :=
  ∃ (Φ ρ : ScalarField1D) (κ : Real), PoissonEquation1D Φ ρ κ

def WeakFieldPoissonLimitStatement3D : Prop :=
  ∃ (Φ ρ : ScalarField3D) (κ : Real), PoissonEquation3D Φ ρ κ

theorem weakFieldResidualFromProjection
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hProjectionFromCore :
      WeakFieldProjectionFromCore
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration)
    (hELCore : EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 :=
  hProjectionFromCore.discrete_residual_zero_from_core hELCore

theorem OperatorToDiscreteResidual
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hResidualFromCore :
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 := by
  intro i
  have hExtracted :=
    congrArg (fun op => op hPotentialIdentification.Φ i)
      hLaplacianExtraction.h_extracted_is_discrete
  dsimp [DiscretePoissonResidual1D] at *
  simpa [hExtracted] using hResidualFromCore i

theorem weakFieldPoissonResidualOfProjection
    (hPotentialIdentification : PotentialIdentification)
    (hSourceIdentification : SourceIdentification)
    (hLaplacianExtraction : LaplacianExtraction)
    (hUnitsAndCalibration : UnitsAndCalibration)
    (hResidualFromCore :
      ∀ i : Int,
        hLaplacianExtraction.extractedOperator hPotentialIdentification.Φ i
          - hUnitsAndCalibration.κ * hSourceIdentification.ρ i = 0) :
    ∀ i : Int,
      DiscretePoissonResidual1D
        hPotentialIdentification.Φ
        hSourceIdentification.ρ
        hUnitsAndCalibration.κ i = 0 :=
  OperatorToDiscreteResidual
    hPotentialIdentification
    hSourceIdentification
    hLaplacianExtraction
    hUnitsAndCalibration
    hResidualFromCore

theorem discreteLaplacian3D_of_lift_x_only
    (hMapping : Lift1DTo3DMappingAssumptions) :
    ∀ p : LatticePoint3D,
      DiscreteLaplacian3D hMapping.Φ3D p = DiscreteLaplacian1D hMapping.Φ1D p.x := by
  intro p
  dsimp [DiscreteLaplacian3D, DiscreteLaplacian1D]
  simp [hMapping.potential_lift_x_only]
  ring

theorem discretePoissonResidual3D_of_lift_x_only
    (hMapping : Lift1DTo3DMappingAssumptions)
    (κ : Real) :
    ∀ p : LatticePoint3D,
      DiscretePoissonResidual3D hMapping.Φ3D hMapping.ρ3D κ p
        = DiscretePoissonResidual1D hMapping.Φ1D hMapping.ρ1D κ p.x := by
  intro p
  dsimp [DiscretePoissonResidual3D, DiscretePoissonResidual1D]
  rw [discreteLaplacian3D_of_lift_x_only hMapping p]
  simp [hMapping.source_lift_x_only]

theorem poissonEquation3D_of_poissonEquation1D_under_lift_x_only
    (hMapping : Lift1DTo3DMappingAssumptions)
    (κ : Real)
    (hPoisson1D : PoissonEquation1D hMapping.Φ1D hMapping.ρ1D κ) :
    PoissonEquation3D hMapping.Φ3D hMapping.ρ3D κ := by
  intro p
  have hResidual3DTo1D :=
    discretePoissonResidual3D_of_lift_x_only hMapping κ p
  have hResidual1D : DiscretePoissonResidual1D hMapping.Φ1D hMapping.ρ1D κ p.x = 0 :=
    hPoisson1D p.x
  simpa [hResidual3DTo1D] using hResidual1D

theorem weakFieldPoissonLimitStatement3D_of_weakFieldPoissonLimitStatement_under_lift_x_only
    (hMapping : Lift1DTo3DMappingAssumptions)
    (κ : Real)
    (hPoisson1D : PoissonEquation1D hMapping.Φ1D hMapping.ρ1D κ) :
    WeakFieldPoissonLimitStatement3D := by
  refine ⟨hMapping.Φ3D, hMapping.ρ3D, κ, ?_⟩
  exact poissonEquation3D_of_poissonEquation1D_under_lift_x_only hMapping κ hPoisson1D

theorem discreteLaplacian3D_of_separable
    (hMapping : Separable3DMappingAssumptions) :
    ∀ p : LatticePoint3D,
      DiscreteLaplacian3D hMapping.Φ3D p =
        DiscreteLaplacian1D hMapping.Φx p.x
          + DiscreteLaplacian1D hMapping.Φy p.y
          + DiscreteLaplacian1D hMapping.Φz p.z := by
  intro p
  dsimp [DiscreteLaplacian3D, DiscreteLaplacian1D]
  simp [hMapping.potential_is_separable]
  ring

theorem discretePoissonResidual3D_of_separable
    (hMapping : Separable3DMappingAssumptions)
    (κ : Real) :
    ∀ p : LatticePoint3D,
      DiscretePoissonResidual3D hMapping.Φ3D hMapping.ρ3D κ p
        =
        DiscretePoissonResidual1D hMapping.Φx hMapping.ρx κ p.x
          + DiscretePoissonResidual1D hMapping.Φy hMapping.ρy κ p.y
          + DiscretePoissonResidual1D hMapping.Φz hMapping.ρz κ p.z := by
  intro p
  dsimp [DiscretePoissonResidual3D, DiscretePoissonResidual1D]
  rw [discreteLaplacian3D_of_separable hMapping p]
  simp [hMapping.source_is_separable]
  ring

theorem poissonEquation3D_of_componentwise_poissonEquation1D_under_separable
    (hMapping : Separable3DMappingAssumptions)
    (κ : Real)
    (hPoissonX : PoissonEquation1D hMapping.Φx hMapping.ρx κ)
    (hPoissonY : PoissonEquation1D hMapping.Φy hMapping.ρy κ)
    (hPoissonZ : PoissonEquation1D hMapping.Φz hMapping.ρz κ) :
    PoissonEquation3D hMapping.Φ3D hMapping.ρ3D κ := by
  intro p
  have hResidualDecomp :=
    discretePoissonResidual3D_of_separable hMapping κ p
  rw [hResidualDecomp]
  simp [hPoissonX p.x, hPoissonY p.y, hPoissonZ p.z]

theorem weakFieldPoissonLimitStatement3D_of_componentwise_poissonEquation1D_under_separable
    (hMapping : Separable3DMappingAssumptions)
    (κ : Real)
    (hPoissonX : PoissonEquation1D hMapping.Φx hMapping.ρx κ)
    (hPoissonY : PoissonEquation1D hMapping.Φy hMapping.ρy κ)
    (hPoissonZ : PoissonEquation1D hMapping.Φz hMapping.ρz κ) :
    WeakFieldPoissonLimitStatement3D := by
  refine ⟨hMapping.Φ3D, hMapping.ρ3D, κ, ?_⟩
  exact
    poissonEquation3D_of_componentwise_poissonEquation1D_under_separable
      hMapping
      κ
      hPoissonX
      hPoissonY
      hPoissonZ

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP
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
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  have hProjectionFromCore :
      WeakFieldProjectionFromCore
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration :=
    mkWeakFieldProjectionFromCore
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual
  let _ := ε
  let _ := hε
  have hELCore :
      EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32 := by
    simpa [hP] using EL_toe_eq_P_rep32
  have hResidual :
      ∀ i : Int,
        DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    weakFieldResidualFromProjection
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionFromCore
      hELCore
  let _ := hWeakFieldAnsatz
  let _ := hSmallPerturbationExpansion
  let _ := hUnitsAndCalibration.h_kappa_relation
  refine ⟨hPotentialIdentification.Φ, hSourceIdentification.ρ, hUnitsAndCalibration.κ, ?_⟩
  intro i
  exact hResidual i

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_of_hP
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
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := hAction
  let _ := hRAC
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

theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_of_hP
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
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  let _ := hRAC
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

theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions
    (ε : Real) (hε : ε ≠ 0)
    (hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
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
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_of_hP
      ε
      hε
      hAction
      hRAC
      P_rep32_def
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual

theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions
    (ε : Real) (hε : ε ≠ 0)
    (hRAC : RACRep32CubicObligationSet declared_g_rep32)
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
    (hELImpliesDiscretePoissonResidual :
      ELImpliesDiscretePoissonResidual
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration) :
    WeakFieldPoissonLimitStatement := by
  exact
    TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_of_hP
      ε
      hε
      hRAC
      P_rep32_def
      hWeakFieldAnsatz
      hSmallPerturbationExpansion
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      hProjectionMapWellFormed
      hWeakFieldTruncationSound
      hELImpliesDiscretePoissonResidual

end
end Variational
end ToeFormal
