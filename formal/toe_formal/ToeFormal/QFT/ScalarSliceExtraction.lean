/-
ToeFormal/QFT/ScalarSliceExtraction.lean

Bounded bridge from the candidate master-action working form to the strict
scalar first-variation backbone.

Scope:
- free-scalar regime projection/extraction theorem target
- reuse theorem from the projected scalar action to the continuum KG-class
  residual equation
- no canonical master-action promotion
- no seam closure, empirical claim, publication packaging, gauge/Standard Model
  extension, or claim that continuum analytic assumptions are discharged

The bridge is intentionally narrow: if a retained projection witness reduces the
candidate master action to the already-formalized scalar quadratic action, then
the landed continuum first-variation theorem supplies the KG-class residual
conclusion under the same explicit analytic obligations.
-/

import ToeFormal.QFT.ContinuumFirstVariation

namespace ToeFormal
namespace QFT
namespace ScalarSliceExtraction

open ContinuumFirstVariation
set_option autoImplicit false

noncomputable section

/-- Abstract working-form candidate master action over a master configuration. -/
structure CandidateMasterActionSurface (MasterConfig : Type) where
  action : MasterConfig → Real

/--
Free-scalar regime projection from a continuum scalar field into a master-action
configuration, together with named retained regime assumptions.
-/
structure FreeScalarRegimeProjection (Point MasterConfig : Type) where
  regimeTag : String
  embedScalarField : ContinuumField Point → MasterConfig
  scalarSliceSelected : Prop
  nonScalarBlocksNeutral : Prop
  coefficientsFixed : Prop
  interactionDerivativeZero : Prop
  seamTermsInactive : Prop

/-- Witness that the retained free-scalar regime assumptions are in force. -/
structure FreeScalarRegimeWitness {Point MasterConfig : Type}
    (projection : FreeScalarRegimeProjection Point MasterConfig) where
  scalar_slice_selected : projection.scalarSliceSelected
  non_scalar_blocks_neutral : projection.nonScalarBlocksNeutral
  coefficients_fixed : projection.coefficientsFixed
  interaction_derivative_zero : projection.interactionDerivativeZero
  seam_terms_inactive : projection.seamTermsInactive

/--
Narrow scalar-slice extraction bridge.

The key nontrivial retained input is `action_reduces_to_scalar`: under the
projection witness, the master action evaluated on embedded scalar fields is
exactly the continuum scalar quadratic action already formalized in the strict
physics lane.
-/
structure ScalarSliceExtractionBridge {Point MasterConfig : Type}
    (master : CandidateMasterActionSurface MasterConfig)
    (projection : FreeScalarRegimeProjection Point MasterConfig)
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real) where
  regime_witness : FreeScalarRegimeWitness projection
  continuum_obligations : ContinuumFirstVariationObligations integral operator
  action_reduces_to_scalar :
    ∀ phi : ContinuumField Point,
      master.action (projection.embedScalarField phi) =
        Action integral operator massSq phi

/-- Master action path along an embedded scalar variation family. -/
def ProjectedMasterActionPath {Point MasterConfig : Type}
    (master : CandidateMasterActionSurface MasterConfig)
    (projection : FreeScalarRegimeProjection Point MasterConfig)
    (phi eta : ContinuumField Point) (eps : Real) : Real :=
  master.action (projection.embedScalarField (VariationFamily phi eta eps))

/-- The scalar first variation, interpreted as the projected master derivative. -/
def ProjectedMasterFirstVariation {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi eta : ContinuumField Point) : Real :=
  FirstVariation integral operator massSq phi eta

/-- Stationarity of the projected master action in the scalar slice. -/
def ProjectedMasterStationary {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi : ContinuumField Point) : Prop :=
  ∀ eta : ContinuumField Point,
    ProjectedMasterFirstVariation integral operator massSq phi eta = 0

/-- Projection/extraction theorem: the bridge yields scalar-action equality. -/
theorem projection_extraction_eq_scalar_action {Point MasterConfig : Type}
    (master : CandidateMasterActionSurface MasterConfig)
    (projection : FreeScalarRegimeProjection Point MasterConfig)
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (extraction : ScalarSliceExtractionBridge master projection integral operator massSq)
    (phi : ContinuumField Point) :
    master.action (projection.embedScalarField phi) =
      Action integral operator massSq phi :=
  extraction.action_reduces_to_scalar phi

/--
Reuse theorem, derivative form: after scalar-slice extraction, the projected
master-action path has the scalar first variation as its algebraic derivative
at zero.
-/
theorem projected_master_action_has_scalar_derivative {Point MasterConfig : Type}
    (master : CandidateMasterActionSurface MasterConfig)
    (projection : FreeScalarRegimeProjection Point MasterConfig)
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (extraction : ScalarSliceExtractionBridge master projection integral operator massSq)
    (phi eta : ContinuumField Point) :
    HasAlgebraicDerivativeAtZero
      (ProjectedMasterActionPath master projection phi eta)
      (master.action (projection.embedScalarField phi))
      (ProjectedMasterFirstVariation integral operator massSq phi eta) := by
  refine ⟨Action integral operator massSq eta, ?_⟩
  intro eps
  unfold ProjectedMasterActionPath ProjectedMasterFirstVariation
  rw [extraction.action_reduces_to_scalar (VariationFamily phi eta eps)]
  rw [extraction.action_reduces_to_scalar phi]
  exact action_shift_expansion
    integral operator extraction.continuum_obligations massSq eps phi eta

/--
Reuse theorem, residual form: projected master-action stationarity in the
free-scalar slice implies the continuum KG-class scalar residual equation.
-/
theorem projected_master_stationary_implies_scalar_kg {Point MasterConfig : Type}
    (master : CandidateMasterActionSurface MasterConfig)
    (projection : FreeScalarRegimeProjection Point MasterConfig)
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (extraction : ScalarSliceExtractionBridge master projection integral operator massSq)
    (phi : ContinuumField Point)
    (hStationary : ProjectedMasterStationary integral operator massSq phi) :
    ResidualEquation (Residual operator massSq phi) := by
  apply continuum_stationary_implies_kg_residual
    integral operator extraction.continuum_obligations massSq phi
  intro eta
  exact hStationary eta

end
end ScalarSliceExtraction
end QFT
end ToeFormal
