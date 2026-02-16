/-
ToeFormal/Variational/GR01Mainstream3DSpherical.lean

Track-A partial theorem surface for the GR01 mainstream-class 3D closure gate.

Scope:
- Explicit spherical-symmetry assumptions and bounded-shell posture.
- Contract-level transport from radial residual closure to 3D residual closure.
- No full 3D Newtonian-limit closure claim.
- No Green-function/point-source closure claim.

Future discharge target (not implemented in this module):
- Replace `laplacian_reduces_to_radial` assumption-field usage with a derived
  stencil-level reduction theorem under explicit lattice spherical-symmetry predicates.
-/

import Mathlib
import ToeFormal.Variational.WeakFieldPoissonLimit

namespace ToeFormal
namespace Variational

noncomputable section
set_option autoImplicit false

abbrev RadialField := ScalarField1D

def DiscreteRadialLaplacian (Φr : RadialField) : RadialField :=
  DiscreteLaplacian1D Φr

def DiscretePoissonResidualRadial (Φr ρr : RadialField) (κ : Real) : RadialField :=
  DiscretePoissonResidual1D Φr ρr κ

def PoissonEquationRadial (Φr ρr : RadialField) (κ : Real) : Prop :=
  PoissonEquation1D Φr ρr κ

def RadialAwayFromSource (sourceIndex : Int) (i : Int) : Prop :=
  i ≠ sourceIndex

def RadialPoissonEquationAwayFromSource
    (Φr ρr : RadialField)
    (κ : Real)
    (sourceIndex : Int) : Prop :=
  ∀ i : Int,
    RadialAwayFromSource sourceIndex i →
    DiscretePoissonResidualRadial Φr ρr κ i = 0

def RadialPoissonEquationAwayFromSourceWithinBound
    (Φr ρr : RadialField)
    (κ : Real)
    (sourceIndex radiusBound : Int) : Prop :=
  ∀ i : Int,
    |i| ≤ |radiusBound| →
    RadialAwayFromSource sourceIndex i →
    DiscretePoissonResidualRadial Φr ρr κ i = 0

structure SphericalPointSourceModelAssumptions where
  sourceIndex : Int
  sourceMass : Real
  ρradial : RadialField
  delta_or_shell_posture :
    ρradial sourceIndex = sourceMass ∧
      (∀ i : Int, i ≠ sourceIndex → ρradial i = 0)

structure SphericalSymmetryMappingAssumptions where
  radialIndex : LatticePoint3D → Int
  Φradial : RadialField
  ρradial : RadialField
  Φ3D : ScalarField3D
  ρ3D : ScalarField3D
  potential_is_radial :
    ∀ p : LatticePoint3D, Φ3D p = Φradial (radialIndex p)
  source_is_radial :
    ∀ p : LatticePoint3D, ρ3D p = ρradial (radialIndex p)
  radial_shell_bound :
    ∃ radiusBound : Int, ∀ p : LatticePoint3D, |radialIndex p| ≤ |radiusBound|
  laplacian_reduces_to_radial :
    ∀ p : LatticePoint3D,
      DiscreteLaplacian3D Φ3D p = DiscreteRadialLaplacian Φradial (radialIndex p)

structure SphericalOperatorEquationAwayFromSourceAssumptions where
  mapping : SphericalSymmetryMappingAssumptions
  sourceIndex : Int
  κ : Real
  radiusBound : Int
  radial_shell_bound :
    ∀ p : LatticePoint3D, |mapping.radialIndex p| ≤ |radiusBound|
  radial_index_realized_within_bound :
    ∀ i : Int,
      |i| ≤ |radiusBound| →
      ∃ p : LatticePoint3D, mapping.radialIndex p = i
  operator_equation_3d_away_from_source :
    ∀ p : LatticePoint3D,
      mapping.radialIndex p ≠ sourceIndex →
      DiscreteLaplacian3D mapping.Φ3D p = κ * mapping.ρ3D p

theorem gr01_mainstream3d_discrete_laplacian_reduces_to_radial_under_spherical_symmetry
    (hMapping : SphericalSymmetryMappingAssumptions) :
    ∀ p : LatticePoint3D,
      DiscreteLaplacian3D hMapping.Φ3D p =
        DiscreteRadialLaplacian hMapping.Φradial (hMapping.radialIndex p) :=
  hMapping.laplacian_reduces_to_radial

theorem gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real) :
    ∀ p : LatticePoint3D,
      DiscretePoissonResidual3D hMapping.Φ3D hMapping.ρ3D κ p =
        DiscretePoissonResidualRadial
          hMapping.Φradial
          hMapping.ρradial
          κ
          (hMapping.radialIndex p) := by
  intro p
  dsimp [DiscretePoissonResidual3D, DiscretePoissonResidualRadial]
  rw [hMapping.laplacian_reduces_to_radial p]
  simp [hMapping.source_is_radial, DiscreteRadialLaplacian, DiscretePoissonResidual1D]

theorem
    gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry
    (hOp : SphericalOperatorEquationAwayFromSourceAssumptions) :
    RadialPoissonEquationAwayFromSourceWithinBound
      hOp.mapping.Φradial
      hOp.mapping.ρradial
      hOp.κ
      hOp.sourceIndex
      hOp.radiusBound := by
  intro i hiBound hiSource
  rcases hOp.radial_index_realized_within_bound i hiBound with ⟨p, hpIndex⟩
  have hpNotSource : hOp.mapping.radialIndex p ≠ hOp.sourceIndex := by
    simpa [hpIndex] using hiSource
  have h3dEquation :
      DiscreteLaplacian3D hOp.mapping.Φ3D p =
        hOp.κ * hOp.mapping.ρ3D p :=
    hOp.operator_equation_3d_away_from_source p hpNotSource
  have hSourceRadial :
      hOp.mapping.ρ3D p = hOp.mapping.ρradial i := by
    simpa [hpIndex] using hOp.mapping.source_is_radial p
  have hRadialEquation :
      DiscreteRadialLaplacian hOp.mapping.Φradial i =
        hOp.κ * hOp.mapping.ρradial i := by
    calc
      DiscreteRadialLaplacian hOp.mapping.Φradial i
          = DiscreteLaplacian3D hOp.mapping.Φ3D p := by
            simpa [hpIndex] using (hOp.mapping.laplacian_reduces_to_radial p).symm
      _ = hOp.κ * hOp.mapping.ρ3D p := h3dEquation
      _ = hOp.κ * hOp.mapping.ρradial i := by simpa [hSourceRadial]
  unfold DiscretePoissonResidualRadial
  unfold DiscretePoissonResidual1D
  exact sub_eq_zero.mpr hRadialEquation

theorem gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (hPoissonRadial : PoissonEquationRadial hMapping.Φradial hMapping.ρradial κ) :
    PoissonEquation3D hMapping.Φ3D hMapping.ρ3D κ := by
  intro p
  have hResidualReduction :=
    gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry
      hMapping
      κ
      p
  have hRadialResidual :
      DiscretePoissonResidualRadial
        hMapping.Φradial
        hMapping.ρradial
        κ
        (hMapping.radialIndex p) = 0 :=
    hPoissonRadial (hMapping.radialIndex p)
  simpa [hResidualReduction] using hRadialResidual

theorem gr01_mainstream3d_spherical_partial_surface_token
    (hMapping : SphericalSymmetryMappingAssumptions)
    (κ : Real)
    (hPoissonRadial : PoissonEquationRadial hMapping.Φradial hMapping.ρradial κ) :
    WeakFieldPoissonLimitStatement3D := by
  refine ⟨hMapping.Φ3D, hMapping.ρ3D, κ, ?_⟩
  exact
    gr01_mainstream3d_poissonEquation3D_of_radial_poisson_under_spherical_symmetry
      hMapping
      κ
      hPoissonRadial

theorem gr01_mainstream3d_point_source_model_discrete_delta_or_shell
    (hSource : SphericalPointSourceModelAssumptions) :
    hSource.ρradial hSource.sourceIndex = hSource.sourceMass ∧
      (∀ i : Int, i ≠ hSource.sourceIndex → hSource.ρradial i = 0) :=
  hSource.delta_or_shell_posture

structure SphericalGreenClassPartialAssumptions where
  operatorBridge : SphericalOperatorEquationAwayFromSourceAssumptions
  sourceModel : SphericalPointSourceModelAssumptions
  source_index_agrees :
    sourceModel.sourceIndex = operatorBridge.sourceIndex
  source_profile_agrees :
    sourceModel.ρradial = operatorBridge.mapping.ρradial

theorem gr01_mainstream3d_green_class_partial_surface_token
    (hGreen : SphericalGreenClassPartialAssumptions) :
    ∃ radiusBound : Int,
      (∀ p : LatticePoint3D, |hGreen.operatorBridge.mapping.radialIndex p| ≤ |radiusBound|) ∧
      RadialPoissonEquationAwayFromSourceWithinBound
        hGreen.operatorBridge.mapping.Φradial
        hGreen.operatorBridge.mapping.ρradial
        hGreen.operatorBridge.κ
        hGreen.sourceModel.sourceIndex
        radiusBound ∧
      (hGreen.sourceModel.ρradial hGreen.sourceModel.sourceIndex = hGreen.sourceModel.sourceMass ∧
        (∀ i : Int, i ≠ hGreen.sourceModel.sourceIndex →
          hGreen.sourceModel.ρradial i = 0)) := by
  let radiusBound : Int := hGreen.operatorBridge.radiusBound
  have hBound :
      ∀ p : LatticePoint3D,
        |hGreen.operatorBridge.mapping.radialIndex p| ≤ |radiusBound| := by
    simpa [radiusBound] using hGreen.operatorBridge.radial_shell_bound
  have hRadialAwayFromSource :
      RadialPoissonEquationAwayFromSourceWithinBound
        hGreen.operatorBridge.mapping.Φradial
        hGreen.operatorBridge.mapping.ρradial
        hGreen.operatorBridge.κ
        hGreen.sourceModel.sourceIndex
        radiusBound := by
    simpa [hGreen.source_index_agrees] using
      gr01_mainstream3d_radial_poisson_away_from_source_from_operator_equation_under_spherical_symmetry
        hGreen.operatorBridge
  exact
    ⟨radiusBound, hBound, hRadialAwayFromSource,
      gr01_mainstream3d_point_source_model_discrete_delta_or_shell hGreen.sourceModel⟩

end
end Variational
end ToeFormal
