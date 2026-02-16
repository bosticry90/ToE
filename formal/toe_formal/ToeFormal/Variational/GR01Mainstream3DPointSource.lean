/-
ToeFormal/Variational/GR01Mainstream3DPointSource.lean

Track-B partial theorem surface for the GR01 mainstream-class 3D closure gate.

Scope:
- Explicit point-source (delta-like) source posture on the 3D lattice.
- Explicit bounded-domain and bounded-behavior contract posture.
- Contract-level transport from point-source residual closure to `PoissonEquation3D`.
- No continuum-limit claim.
- No infinite-domain Green-function inversion claim.
- No full uniqueness/fundamental-solution claim.
-/

import Mathlib
import ToeFormal.Variational.WeakFieldPoissonLimit

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

structure PointSourceMappingAssumptions where
  sourceCenter : LatticePoint3D
  sourceMass : Real
  κ : Real
  Φ3D : ScalarField3D
  ρ3D : ScalarField3D
  latticeNorm : LatticePoint3D → Int
  delta_posture :
    ρ3D sourceCenter = sourceMass ∧
      (∀ p : LatticePoint3D, p ≠ sourceCenter → ρ3D p = 0)
  bounded_domain :
    ∃ radiusBound : Int, ∀ p : LatticePoint3D, |latticeNorm p| ≤ |radiusBound|
  bounded_potential_behavior :
    ∃ potentialBound : Real, ∀ p : LatticePoint3D, |Φ3D p| ≤ potentialBound
  residual_zero_under_point_source :
    ∀ p : LatticePoint3D, DiscretePoissonResidual3D Φ3D ρ3D κ p = 0

theorem gr01_mainstream3d_point_source_delta_posture_is_explicit
    (hPoint : PointSourceMappingAssumptions) :
    hPoint.ρ3D hPoint.sourceCenter = hPoint.sourceMass ∧
      (∀ p : LatticePoint3D, p ≠ hPoint.sourceCenter → hPoint.ρ3D p = 0) :=
  hPoint.delta_posture

theorem gr01_mainstream3d_point_source_bounded_domain_posture
    (hPoint : PointSourceMappingAssumptions) :
    ∃ radiusBound : Int, ∀ p : LatticePoint3D, |hPoint.latticeNorm p| ≤ |radiusBound| :=
  hPoint.bounded_domain

theorem gr01_mainstream3d_point_source_bounded_potential_behavior_posture
    (hPoint : PointSourceMappingAssumptions) :
    ∃ potentialBound : Real, ∀ p : LatticePoint3D, |hPoint.Φ3D p| ≤ potentialBound :=
  hPoint.bounded_potential_behavior

theorem gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture
    (hPoint : PointSourceMappingAssumptions) :
    PoissonEquation3D hPoint.Φ3D hPoint.ρ3D hPoint.κ :=
  hPoint.residual_zero_under_point_source

theorem gr01_mainstream3d_point_source_partial_surface_token
    (hPoint : PointSourceMappingAssumptions) :
    WeakFieldPoissonLimitStatement3D := by
  refine ⟨hPoint.Φ3D, hPoint.ρ3D, hPoint.κ, ?_⟩
  exact gr01_mainstream3d_point_source_poissonEquation3D_under_bounded_delta_posture hPoint

structure PointSourceDirichletBoundaryAssumptions where
  sourceCenter : LatticePoint3D
  sourceMass : Real
  κ : Real
  Φcandidate : ScalarField3D
  ρcandidate : ScalarField3D
  inDomain : LatticePoint3D → Prop
  onBoundary : LatticePoint3D → Prop
  boundary_subset_domain :
    ∀ p : LatticePoint3D, onBoundary p → inDomain p
  source_in_domain : inDomain sourceCenter
  source_not_on_boundary : ¬ onBoundary sourceCenter
  delta_posture :
    ρcandidate sourceCenter = sourceMass ∧
      (∀ p : LatticePoint3D, p ≠ sourceCenter → ρcandidate p = 0)
  dirichlet_boundary_zero :
    ∀ p : LatticePoint3D, onBoundary p → Φcandidate p = 0
  residual_zero_away_from_source :
    ∀ p : LatticePoint3D,
      inDomain p →
      p ≠ sourceCenter →
      DiscretePoissonResidual3D Φcandidate ρcandidate κ p = 0
  center_residual_defect_is_explicit :
    ∃ defect : Real,
      DiscretePoissonResidual3D Φcandidate ρcandidate κ sourceCenter = defect

structure PointSourceResidualDischargeUnderDirichlet where
  Φcandidate : ScalarField3D
  ρcandidate : ScalarField3D
  κ : Real
  inDomain : LatticePoint3D → Prop
  onBoundary : LatticePoint3D → Prop
  sourceCenter : LatticePoint3D
  sourceMass : Real
  dirichlet_boundary_zero :
    ∀ p : LatticePoint3D, onBoundary p → Φcandidate p = 0
  residual_zero_away_from_source :
    ∀ p : LatticePoint3D,
      inDomain p →
      p ≠ sourceCenter →
      DiscretePoissonResidual3D Φcandidate ρcandidate κ p = 0
  center_residual_defect_is_explicit :
    ∃ defect : Real,
      DiscretePoissonResidual3D Φcandidate ρcandidate κ sourceCenter = defect

structure FiniteDirichletDomain3D where
  inDomain : LatticePoint3D → Prop
  onBoundary : LatticePoint3D → Prop
  boundary_subset_domain :
    ∀ p : LatticePoint3D, onBoundary p → inDomain p

def IsInteriorPoint
    (domain : FiniteDirichletDomain3D)
    (p : LatticePoint3D) : Prop :=
  domain.inDomain p ∧ ¬ domain.onBoundary p

def PoissonEquation3DAwayFromSourceOnDomain
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D) : Prop :=
  ∀ p : LatticePoint3D,
    IsInteriorPoint domain p →
    p ≠ sourceCenter →
    DiscretePoissonResidual3D Φ ρ κ p = 0

def SatisfiesDirichletPoissonSystemOnDomain
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D) : Prop :=
  (∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0) ∧
    PoissonEquation3DAwayFromSourceOnDomain Φ ρ κ domain sourceCenter

def SatisfiesDirichletLinearSystemOnDomain
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D) : Prop :=
  (∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0) ∧
    (∀ p : LatticePoint3D,
      IsInteriorPoint domain p →
      p ≠ sourceCenter →
      DiscreteLaplacian3D Φ p = κ * ρ p)

structure DirichletLinearOperator3D where
  apply : ScalarField3D → ScalarField3D

def DirichletRHS3D
    (ρ : ScalarField3D)
    (κ : Real) : ScalarField3D :=
  fun p => κ * ρ p

def OperatorEncodesDiscreteLaplacianOnInterior
    (A : DirichletLinearOperator3D)
    (domain : FiniteDirichletDomain3D) : Prop :=
  ∀ Φ : ScalarField3D,
    ∀ p : LatticePoint3D,
      IsInteriorPoint domain p →
      A.apply Φ p = DiscreteLaplacian3D Φ p

def SatisfiesFiniteLinearOperatorEquationOnDomain
    (A : DirichletLinearOperator3D)
    (Φ : ScalarField3D)
    (b : ScalarField3D)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D) : Prop :=
  ∀ p : LatticePoint3D,
    IsInteriorPoint domain p →
    p ≠ sourceCenter →
    A.apply Φ p = b p

def OperatorHasDirichletRightInverseOnDomain
    (A : DirichletLinearOperator3D)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D) : Prop :=
  ∃ Ainv : ScalarField3D → ScalarField3D,
    (∀ b : ScalarField3D,
      ∀ p : LatticePoint3D,
        IsInteriorPoint domain p →
        p ≠ sourceCenter →
        A.apply (Ainv b) p = b p) ∧
    (∀ b : ScalarField3D,
      ∀ p : LatticePoint3D,
        domain.onBoundary p →
        Ainv b p = 0)

structure PointSourceDirichletCandidateSolution where
  Φcandidate : ScalarField3D
  ρcandidate : ScalarField3D
  κ : Real
  sourceCenter : LatticePoint3D
  sourceMass : Real
  domain : FiniteDirichletDomain3D
  source_in_domain : domain.inDomain sourceCenter
  source_not_on_boundary : ¬ domain.onBoundary sourceCenter
  delta_posture :
    ρcandidate sourceCenter = sourceMass ∧
      (∀ p : LatticePoint3D, p ≠ sourceCenter → ρcandidate p = 0)
  system_satisfaction :
    SatisfiesDirichletPoissonSystemOnDomain Φcandidate ρcandidate κ domain sourceCenter

def dirichletDomainOfAssumptions
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    FiniteDirichletDomain3D :=
  {
    inDomain := hDirichlet.inDomain
    onBoundary := hDirichlet.onBoundary
    boundary_subset_domain := hDirichlet.boundary_subset_domain
  }

theorem gr01_mainstream3d_point_source_dirichlet_boundary_posture_is_explicit
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    ∀ p : LatticePoint3D, hDirichlet.onBoundary p → hDirichlet.Φcandidate p = 0 :=
  hDirichlet.dirichlet_boundary_zero

theorem gr01_mainstream3d_point_source_residual_zero_away_from_source_under_dirichlet_boundary
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    ∀ p : LatticePoint3D,
      hDirichlet.inDomain p →
      p ≠ hDirichlet.sourceCenter →
      DiscretePoissonResidual3D
        hDirichlet.Φcandidate
        hDirichlet.ρcandidate
        hDirichlet.κ p = 0 :=
  hDirichlet.residual_zero_away_from_source

theorem gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    ∃ defect : Real,
      DiscretePoissonResidual3D
        hDirichlet.Φcandidate
        hDirichlet.ρcandidate
        hDirichlet.κ hDirichlet.sourceCenter = defect :=
  hDirichlet.center_residual_defect_is_explicit

theorem
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hSystem :
      SatisfiesDirichletPoissonSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter) :
    PoissonEquation3DAwayFromSourceOnDomain
      Φ
      ρ
      κ
      domain
      sourceCenter := by
  exact hSystem.2

theorem gr01_mainstream3d_point_source_system_satisfaction_from_linear_system
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hLinear :
      SatisfiesDirichletLinearSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter) :
    SatisfiesDirichletPoissonSystemOnDomain
      Φ
      ρ
      κ
      domain
      sourceCenter := by
  refine ⟨hLinear.1, ?_⟩
  intro p hpInterior hpNeSource
  have hEq : DiscreteLaplacian3D Φ p = κ * ρ p :=
    hLinear.2 p hpInterior hpNeSource
  unfold DiscretePoissonResidual3D
  exact sub_eq_zero.mpr hEq

theorem gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation
    (A : DirichletLinearOperator3D)
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hBoundary :
      ∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0)
    (hOperatorEncodes :
      OperatorEncodesDiscreteLaplacianOnInterior A domain)
    (hOperatorEquation :
      SatisfiesFiniteLinearOperatorEquationOnDomain
        A
        Φ
        (DirichletRHS3D ρ κ)
        domain
        sourceCenter) :
    SatisfiesDirichletLinearSystemOnDomain
      Φ
      ρ
      κ
      domain
      sourceCenter := by
  refine ⟨hBoundary, ?_⟩
  intro p hpInterior hpNeSource
  have hAeq :
      A.apply Φ p = DirichletRHS3D ρ κ p :=
    hOperatorEquation p hpInterior hpNeSource
  have hAenc :
      A.apply Φ p = DiscreteLaplacian3D Φ p :=
    hOperatorEncodes Φ p hpInterior
  calc
    DiscreteLaplacian3D Φ p = A.apply Φ p := by symm; exact hAenc
    _ = DirichletRHS3D ρ κ p := hAeq
    _ = κ * ρ p := rfl

theorem gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_of_candidate_solution
    (hCandidate : PointSourceDirichletCandidateSolution) :
    PoissonEquation3DAwayFromSourceOnDomain
      hCandidate.Φcandidate
      hCandidate.ρcandidate
      hCandidate.κ
      hCandidate.domain
      hCandidate.sourceCenter :=
  gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system
    hCandidate.Φcandidate
    hCandidate.ρcandidate
    hCandidate.κ
    hCandidate.domain
    hCandidate.sourceCenter
    hCandidate.system_satisfaction

theorem gr01_mainstream3d_point_source_candidate_exists_from_linear_system
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (sourceMass : Real)
    (hSourceInDomain : domain.inDomain sourceCenter)
    (hSourceNotOnBoundary : ¬ domain.onBoundary sourceCenter)
    (hDeltaPosture :
      ρ sourceCenter = sourceMass ∧
        (∀ p : LatticePoint3D, p ≠ sourceCenter → ρ p = 0))
    (hLinear :
      SatisfiesDirichletLinearSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter) :
    ∃ hCandidate : PointSourceDirichletCandidateSolution,
      hCandidate.Φcandidate = Φ ∧
      hCandidate.ρcandidate = ρ ∧
      hCandidate.sourceCenter = sourceCenter := by
  refine ⟨{
    Φcandidate := Φ
    ρcandidate := ρ
    κ := κ
    sourceCenter := sourceCenter
    sourceMass := sourceMass
    domain := domain
    source_in_domain := hSourceInDomain
    source_not_on_boundary := hSourceNotOnBoundary
    delta_posture := hDeltaPosture
    system_satisfaction :=
      gr01_mainstream3d_point_source_system_satisfaction_from_linear_system
        Φ
        ρ
        κ
        domain
        sourceCenter
        hLinear
  }, rfl, rfl, rfl⟩

theorem gr01_mainstream3d_point_source_candidate_exists_from_operator_equation
    (A : DirichletLinearOperator3D)
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (sourceMass : Real)
    (hSourceInDomain : domain.inDomain sourceCenter)
    (hSourceNotOnBoundary : ¬ domain.onBoundary sourceCenter)
    (hDeltaPosture :
      ρ sourceCenter = sourceMass ∧
        (∀ p : LatticePoint3D, p ≠ sourceCenter → ρ p = 0))
    (hBoundary :
      ∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0)
    (hOperatorEncodes :
      OperatorEncodesDiscreteLaplacianOnInterior A domain)
    (hOperatorEquation :
      SatisfiesFiniteLinearOperatorEquationOnDomain
        A
        Φ
        (DirichletRHS3D ρ κ)
        domain
        sourceCenter) :
    ∃ hCandidate : PointSourceDirichletCandidateSolution,
      hCandidate.Φcandidate = Φ ∧
      hCandidate.ρcandidate = ρ ∧
      hCandidate.sourceCenter = sourceCenter := by
  have hOperatorApplyWitness :
      ∀ p : LatticePoint3D,
        IsInteriorPoint domain p →
        p ≠ sourceCenter →
        A.apply Φ p = DirichletRHS3D ρ κ p :=
    hOperatorEquation
  have hLinear :
      SatisfiesDirichletLinearSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter :=
    gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation
      A
      Φ
      ρ
      κ
      domain
      sourceCenter
      hBoundary
      hOperatorEncodes
      hOperatorApplyWitness
  exact
    gr01_mainstream3d_point_source_candidate_exists_from_linear_system
      Φ
      ρ
      κ
      domain
      sourceCenter
      sourceMass
      hSourceInDomain
      hSourceNotOnBoundary
      hDeltaPosture
      hLinear

theorem
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation
    (A : DirichletLinearOperator3D)
    (Φ ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hBoundary :
      ∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0)
    (hOperatorEncodes :
      OperatorEncodesDiscreteLaplacianOnInterior A domain)
    (hOperatorEquation :
      SatisfiesFiniteLinearOperatorEquationOnDomain
        A
        Φ
        (DirichletRHS3D ρ κ)
        domain
        sourceCenter) :
    PoissonEquation3DAwayFromSourceOnDomain
      Φ
      ρ
      κ
      domain
      sourceCenter := by
  have hOperatorApplyWitness :
      ∀ p : LatticePoint3D,
        IsInteriorPoint domain p →
        p ≠ sourceCenter →
        A.apply Φ p = DirichletRHS3D ρ κ p :=
    hOperatorEquation
  have hLinear :
      SatisfiesDirichletLinearSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter :=
    gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation
      A
      Φ
      ρ
      κ
      domain
      sourceCenter
      hBoundary
      hOperatorEncodes
      hOperatorApplyWitness
  have hSystem :
      SatisfiesDirichletPoissonSystemOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter :=
    gr01_mainstream3d_point_source_system_satisfaction_from_linear_system
      Φ
      ρ
      κ
      domain
      sourceCenter
      hLinear
  exact
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system
      Φ
      ρ
      κ
      domain
      sourceCenter
      hSystem

theorem
    gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility
    (A : DirichletLinearOperator3D)
    (ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hInvertible :
      OperatorHasDirichletRightInverseOnDomain
        A
        domain
        sourceCenter) :
    ∃ Φ : ScalarField3D,
      (∀ p : LatticePoint3D, domain.onBoundary p → Φ p = 0) ∧
      SatisfiesFiniteLinearOperatorEquationOnDomain
        A
        Φ
        (DirichletRHS3D ρ κ)
        domain
        sourceCenter := by
  rcases hInvertible with ⟨Ainv, hInterior, hBoundary⟩
  let b : ScalarField3D := DirichletRHS3D ρ κ
  refine ⟨Ainv b, ?_⟩
  constructor
  · intro p hpBoundary
    exact hBoundary b p hpBoundary
  · intro p hpInterior hpNeSource
    exact hInterior b p hpInterior hpNeSource

theorem
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility
    (A : DirichletLinearOperator3D)
    (ρ : ScalarField3D)
    (κ : Real)
    (domain : FiniteDirichletDomain3D)
    (sourceCenter : LatticePoint3D)
    (hOperatorEncodes :
      OperatorEncodesDiscreteLaplacianOnInterior A domain)
    (hInvertible :
      OperatorHasDirichletRightInverseOnDomain
        A
        domain
        sourceCenter) :
    ∃ Φ : ScalarField3D,
      PoissonEquation3DAwayFromSourceOnDomain
        Φ
        ρ
        κ
        domain
        sourceCenter := by
  rcases
      gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility
        A
        ρ
        κ
        domain
        sourceCenter
        hInvertible with
    ⟨Φ, hBoundary, hOperatorEquation⟩
  refine ⟨Φ, ?_⟩
  exact
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation
      A
      Φ
      ρ
      κ
      domain
      sourceCenter
      hBoundary
      hOperatorEncodes
      hOperatorEquation

theorem gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    ∃ discharge : PointSourceResidualDischargeUnderDirichlet,
      discharge.sourceCenter = hDirichlet.sourceCenter := by
  refine
    ⟨{
      Φcandidate := hDirichlet.Φcandidate
      ρcandidate := hDirichlet.ρcandidate
      κ := hDirichlet.κ
      inDomain := hDirichlet.inDomain
      onBoundary := hDirichlet.onBoundary
      sourceCenter := hDirichlet.sourceCenter
      sourceMass := hDirichlet.sourceMass
      dirichlet_boundary_zero := hDirichlet.dirichlet_boundary_zero
      residual_zero_away_from_source := hDirichlet.residual_zero_away_from_source
      center_residual_defect_is_explicit := hDirichlet.center_residual_defect_is_explicit
    }, rfl⟩

theorem gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    ∀ p : LatticePoint3D,
      hDirichlet.inDomain p →
      (p ≠ hDirichlet.sourceCenter →
        DiscretePoissonResidual3D
          hDirichlet.Φcandidate
          hDirichlet.ρcandidate
          hDirichlet.κ p = 0) ∧
      (p = hDirichlet.sourceCenter →
        ∃ defect : Real,
          DiscretePoissonResidual3D
            hDirichlet.Φcandidate
            hDirichlet.ρcandidate
            hDirichlet.κ p = defect) := by
  intro p hpInDomain
  constructor
  · intro hpNeCenter
    exact hDirichlet.residual_zero_away_from_source p hpInDomain hpNeCenter
  · intro hpEqCenter
    subst hpEqCenter
    exact hDirichlet.center_residual_defect_is_explicit

theorem gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary
    (hDirichlet : PointSourceDirichletBoundaryAssumptions) :
    PoissonEquation3DAwayFromSourceOnDomain
      hDirichlet.Φcandidate
      hDirichlet.ρcandidate
      hDirichlet.κ
      (dirichletDomainOfAssumptions hDirichlet)
      hDirichlet.sourceCenter := by
  let domain := dirichletDomainOfAssumptions hDirichlet
  have hSystem :
      SatisfiesDirichletPoissonSystemOnDomain
        hDirichlet.Φcandidate
        hDirichlet.ρcandidate
        hDirichlet.κ
        domain
      hDirichlet.sourceCenter := by
    refine ⟨hDirichlet.dirichlet_boundary_zero, ?_⟩
    intro p hpInterior hpNeSource
    exact hDirichlet.residual_zero_away_from_source p hpInterior.1 hpNeSource
  simpa [domain] using
    gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system
      hDirichlet.Φcandidate
      hDirichlet.ρcandidate
      hDirichlet.κ
      domain
      hDirichlet.sourceCenter
      hSystem

end
end Variational
end ToeFormal
