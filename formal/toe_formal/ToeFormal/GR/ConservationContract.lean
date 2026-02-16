/-
ToeFormal/GR/ConservationContract.lean

Planning-surface contract for GR conservation object scaffolding.

Scope:
- Contract-only theorem surface.
- Typed GR conservation objects only.
- No GR field-equation claim and no external truth claim.
- No Noether theorem derivation claim.
-/

import Mathlib
import ToeFormal.Variational.WeakFieldPoissonLimit
import ToeFormal.Variational.GR01BridgePromotion

namespace ToeFormal
namespace GR

noncomputable section
set_option autoImplicit false

structure FlowContext (Point : Type) where
  flow : Point → Point

structure DivergenceOperator (Point : Type) where
  divergence : (Point → Real) → Point → Real

structure ConservedQuantity (Point : Type) where
  density : Point → Real

def ConservationLawUnderFlow
    {Point : Type}
    (ctx : FlowContext Point)
    (divergenceOp : DivergenceOperator Point)
    (quantity : ConservedQuantity Point) : Prop :=
  ∀ p : Point, divergenceOp.divergence quantity.density (ctx.flow p) = 0

theorem gr_conservation_under_contract_assumptions
    (Point : Type)
    (ctx : FlowContext Point)
    (divergenceOp : DivergenceOperator Point)
    (quantity : ConservedQuantity Point)
    (h_conservation_under_flow : ConservationLawUnderFlow ctx divergenceOp quantity) :
    ConservationLawUnderFlow ctx divergenceOp quantity :=
  h_conservation_under_flow

abbrev ScalarField1D := ToeFormal.Variational.ScalarField1D

def DiscreteGradient1D (Φ : ScalarField1D) : ScalarField1D :=
  fun i => Φ (i + 1) - Φ i

def DiscreteDivergence1D (g : ScalarField1D) : ScalarField1D :=
  fun i => g i - g (i - 1)

def PoissonFluxCompatibility1D (Φ ρ : ScalarField1D) (κ : Real) : Prop :=
  ∀ i : Int, DiscreteDivergence1D (fun j => -DiscreteGradient1D Φ j) i + κ * ρ i = 0

/--
Contract-level compatibility theorem:
if the 1D discrete Poisson residual closes, then the induced flux-form
divergence/source compatibility closes pointwise.
-/
theorem gr01_conservation_compatibility_from_poisson_residual_v0
    (Φ ρ : ScalarField1D)
    (κ : Real)
    (hResidual :
      ∀ i : Int, ToeFormal.Variational.DiscretePoissonResidual1D Φ ρ κ i = 0) :
    PoissonFluxCompatibility1D Φ ρ κ := by
  intro i
  have hLaplacianEq :
      ToeFormal.Variational.DiscreteLaplacian1D Φ i = κ * ρ i := by
    have hResidualAtI :
        ToeFormal.Variational.DiscretePoissonResidual1D Φ ρ κ i = 0 := hResidual i
    dsimp [ToeFormal.Variational.DiscretePoissonResidual1D] at hResidualAtI
    linarith
  have hFlux :
      DiscreteDivergence1D (fun j => -DiscreteGradient1D Φ j) i =
        -ToeFormal.Variational.DiscreteLaplacian1D Φ i := by
    dsimp [DiscreteDivergence1D, DiscreteGradient1D, ToeFormal.Variational.DiscreteLaplacian1D]
    have hIndex : i - 1 + 1 = i := by omega
    rw [hIndex]
    ring
  calc
    DiscreteDivergence1D (fun j => -DiscreteGradient1D Φ j) i + κ * ρ i
        = -ToeFormal.Variational.DiscreteLaplacian1D Φ i + κ * ρ i := by
          simp [hFlux]
    _ = 0 := by linarith [hLaplacianEq]

/--
Bridge-promotion compatibility theorem:
under the explicit GR01 bridge assumptions, the induced weak-field
discrete divergence/source compatibility surface closes pointwise.
-/
theorem gr01_conservation_compatibility_from_bridge_promotion_chain_v0
    (ε : Real)
    (hε : ε ≠ 0)
    (hAction :
      ToeFormal.Variational.actionRep32.action =
        ToeFormal.Variational.actionRep32Cubic ToeFormal.Variational.declared_g_rep32)
    (hRAC :
      ToeFormal.Variational.RACRep32CubicObligationSet
        ToeFormal.Variational.declared_g_rep32)
    (hPotentialIdentification : ToeFormal.Variational.PotentialIdentification)
    (hSourceIdentification : ToeFormal.Variational.SourceIdentification)
    (hLaplacianExtraction : ToeFormal.Variational.LaplacianExtraction)
    (hUnitsAndCalibration : ToeFormal.Variational.UnitsAndCalibration)
    (phiBound rhoBound : Real)
    (hWeakFieldUniformBound :
      ToeFormal.Variational.WeakFieldUniformBound
        hPotentialIdentification
        hSourceIdentification
        phiBound
        rhoBound)
    (hFirstOrderRemainderSuppressed :
      ToeFormal.Variational.FirstOrderRemainderSuppressed
        hPotentialIdentification
        hLaplacianExtraction)
    (hELImpliesOperatorResidualUnderBound :
      ToeFormal.Variational.ELImpliesOperatorResidualUnderBound
        hPotentialIdentification
        hSourceIdentification
        hLaplacianExtraction
        hUnitsAndCalibration
        phiBound
        rhoBound) :
    PoissonFluxCompatibility1D
      hPotentialIdentification.Φ
      hSourceIdentification.ρ
      hUnitsAndCalibration.κ := by
  have hResidual :
      ∀ i : Int,
        ToeFormal.Variational.DiscretePoissonResidual1D
          hPotentialIdentification.Φ
          hSourceIdentification.ρ
          hUnitsAndCalibration.κ i = 0 :=
    ToeFormal.Variational.gr01_discrete_residual_from_bridge_promotion_chain
      ε
      hε
      hAction
      hRAC
      hPotentialIdentification
      hSourceIdentification
      hLaplacianExtraction
      hUnitsAndCalibration
      phiBound
      rhoBound
      hWeakFieldUniformBound
      hFirstOrderRemainderSuppressed
      hELImpliesOperatorResidualUnderBound
  exact gr01_conservation_compatibility_from_poisson_residual_v0
    hPotentialIdentification.Φ
    hSourceIdentification.ρ
    hUnitsAndCalibration.κ
    hResidual

end
end GR
end ToeFormal
