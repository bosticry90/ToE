/-
ToeFormal/QFT/ConcreteScalarSliceExtraction.lean

Concrete bounded instantiation of the scalar-slice extraction bridge.

Scope:
- define a decomposed candidate master-action surface with scalar kinetic/mass
  coefficients plus explicit non-scalar, interaction, and seam blocks
- define the free-scalar projection that keeps the scalar field, fixes the
  scalar coefficients, and zeros the excluded blocks
- prove `action_reduces_to_scalar` for this decomposed formal surface
- reuse `ScalarSliceExtraction.lean` to obtain the continuum KG-class residual
  conclusion under the same continuum analytic obligations
- no canonical master-action promotion, seam closure, empirical claim,
  publication packaging, gauge/Standard Model extension, or claim that the
  document-level master action has been fully formalized

This file discharges the bridge equality for a concrete decomposed formal
candidate action. The remaining physics obligation is to justify that the
document-level working master action is represented by this decomposition under
the stated free-scalar regime assumptions.
-/

import ToeFormal.QFT.ScalarSliceExtraction

namespace ToeFormal
namespace QFT
namespace ConcreteScalarSliceExtraction

open ContinuumFirstVariation
open ScalarSliceExtraction
set_option autoImplicit false

noncomputable section

/--
Decomposed master-action configuration for the bounded scalar-slice theorem.

The non-scalar blocks collect geometry, gauge, matter, statistical, transport,
and other non-scalar terms at the level needed for the scalar projection. The
interaction and seam blocks are kept separate because the free-scalar regime
must state their deactivation explicitly.
-/
structure DecomposedMasterConfig (Point : Type) where
  scalarField : ContinuumField Point
  kineticCoeff : Real
  massCoeff : Real
  nonScalarBlock : Real
  interactionBlock : Real
  seamBlock : Real

/-- The formal decomposed candidate master action used in this bounded slice. -/
def DecomposedCandidateAction {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (cfg : DecomposedMasterConfig Point) : Real :=
  (1 / 2 : Real) * cfg.kineticCoeff *
      ContinuumPair integral cfg.scalarField (operator cfg.scalarField) +
    (1 / 2 : Real) * cfg.massCoeff *
      ContinuumPair integral cfg.scalarField cfg.scalarField +
    cfg.nonScalarBlock + cfg.interactionBlock + cfg.seamBlock

/-- Candidate master-action surface induced by the decomposed action. -/
def decomposedCandidateMasterAction {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point) :
    CandidateMasterActionSurface (DecomposedMasterConfig Point) where
  action := DecomposedCandidateAction integral operator

/--
Embedding of a scalar field into the free-scalar sector of the decomposed
master configuration.
-/
def freeScalarEmbed {Point : Type}
    (massSq : Real) (phi : ContinuumField Point) :
    DecomposedMasterConfig Point where
  scalarField := phi
  kineticCoeff := 1
  massCoeff := massSq
  nonScalarBlock := 0
  interactionBlock := 0
  seamBlock := 0

/-- The projected scalar component is exactly the input scalar field. -/
def ScalarSliceSelected {Point : Type} (massSq : Real) : Prop :=
  ∀ phi : ContinuumField Point, (freeScalarEmbed massSq phi).scalarField = phi

/-- Non-scalar master-action blocks are neutralized in the free-scalar projection. -/
def NonScalarBlocksNeutral {Point : Type} (massSq : Real) : Prop :=
  ∀ phi : ContinuumField Point, (freeScalarEmbed massSq phi).nonScalarBlock = 0

/-- The scalar kinetic and mass coefficients are fixed to the free-scalar values. -/
def ScalarCoefficientsFixed {Point : Type} (massSq : Real) : Prop :=
  ∀ phi : ContinuumField Point,
    (freeScalarEmbed massSq phi).kineticCoeff = 1 ∧
      (freeScalarEmbed massSq phi).massCoeff = massSq

/-- The interaction block is deactivated in the free-scalar projection. -/
def InteractionDerivativeZero {Point : Type} (massSq : Real) : Prop :=
  ∀ phi : ContinuumField Point, (freeScalarEmbed massSq phi).interactionBlock = 0

/-- Seam-constraint terms are inactive in the free-scalar projection. -/
def SeamTermsInactive {Point : Type} (massSq : Real) : Prop :=
  ∀ phi : ContinuumField Point, (freeScalarEmbed massSq phi).seamBlock = 0

/-- Concrete free-scalar regime projection for the decomposed master action. -/
def freeScalarRegimeProjection {Point : Type}
    (massSq : Real) :
    FreeScalarRegimeProjection Point (DecomposedMasterConfig Point) where
  regimeTag := "decomposed-free-scalar-v0"
  embedScalarField := freeScalarEmbed massSq
  scalarSliceSelected := ScalarSliceSelected (Point := Point) massSq
  nonScalarBlocksNeutral := NonScalarBlocksNeutral (Point := Point) massSq
  coefficientsFixed := ScalarCoefficientsFixed (Point := Point) massSq
  interactionDerivativeZero := InteractionDerivativeZero (Point := Point) massSq
  seamTermsInactive := SeamTermsInactive (Point := Point) massSq

/-- The free-scalar projection witness is constructed for the decomposed model. -/
theorem free_scalar_regime_witness {Point : Type}
    (massSq : Real) :
    FreeScalarRegimeWitness
      (freeScalarRegimeProjection (Point := Point) massSq) := by
  refine
    { scalar_slice_selected := ?_
      non_scalar_blocks_neutral := ?_
      coefficients_fixed := ?_
      interaction_derivative_zero := ?_
      seam_terms_inactive := ?_ }
  · change ScalarSliceSelected (Point := Point) massSq
    intro phi
    rfl
  · change NonScalarBlocksNeutral (Point := Point) massSq
    intro phi
    rfl
  · change ScalarCoefficientsFixed (Point := Point) massSq
    intro phi
    exact ⟨rfl, rfl⟩
  · change InteractionDerivativeZero (Point := Point) massSq
    intro phi
    rfl
  · change SeamTermsInactive (Point := Point) massSq
    intro phi
    rfl

/--
Scalar-term decomposition lemma: after the free-scalar projection, the
decomposed master action is exactly the continuum scalar quadratic action.
-/
theorem decomposed_action_reduces_to_scalar {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (phi : ContinuumField Point) :
    (decomposedCandidateMasterAction integral operator).action
        ((freeScalarRegimeProjection massSq).embedScalarField phi) =
      ContinuumFirstVariation.Action integral operator massSq phi := by
  unfold decomposedCandidateMasterAction DecomposedCandidateAction
  unfold freeScalarRegimeProjection freeScalarEmbed ContinuumFirstVariation.Action
  ring

/--
Concrete scalar-slice extraction bridge for the decomposed candidate action.

This discharges `action_reduces_to_scalar` for the decomposed formal surface;
the continuum first-variation obligations remain exactly the obligations from
`ContinuumFirstVariation.lean`.
-/
def decomposedScalarSliceExtractionBridge {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator) :
    ScalarSliceExtractionBridge
      (decomposedCandidateMasterAction integral operator)
      (freeScalarRegimeProjection massSq)
      integral operator massSq where
  regime_witness := free_scalar_regime_witness massSq
  continuum_obligations := obligations
  action_reduces_to_scalar := by
    intro phi
    exact decomposed_action_reduces_to_scalar integral operator massSq phi

/--
Instantiated bridge theorem: the decomposed free-scalar projection yields scalar
action equality without retaining `action_reduces_to_scalar` as an input.
-/
theorem decomposed_projection_extraction_eq_scalar_action {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator)
    (phi : ContinuumField Point) :
    (decomposedCandidateMasterAction integral operator).action
        ((freeScalarRegimeProjection massSq).embedScalarField phi) =
      ContinuumFirstVariation.Action integral operator massSq phi := by
  exact projection_extraction_eq_scalar_action
    (decomposedCandidateMasterAction integral operator)
    (freeScalarRegimeProjection massSq)
    integral operator massSq
    (decomposedScalarSliceExtractionBridge
      integral operator massSq obligations)
    phi

/--
Instantiated derivative reuse theorem for the decomposed candidate action.
-/
theorem decomposed_projected_master_action_has_scalar_derivative {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator)
    (phi eta : ContinuumField Point) :
    HasAlgebraicDerivativeAtZero
      (ProjectedMasterActionPath
        (decomposedCandidateMasterAction integral operator)
        (freeScalarRegimeProjection massSq) phi eta)
      ((decomposedCandidateMasterAction integral operator).action
        ((freeScalarRegimeProjection massSq).embedScalarField phi))
      (ProjectedMasterFirstVariation integral operator massSq phi eta) := by
  exact projected_master_action_has_scalar_derivative
    (decomposedCandidateMasterAction integral operator)
    (freeScalarRegimeProjection massSq)
    integral operator massSq
    (decomposedScalarSliceExtractionBridge
      integral operator massSq obligations)
    phi eta

/--
Instantiated KG-class conclusion for the decomposed candidate action under
projected free-scalar stationarity.
-/
theorem decomposed_projected_master_stationary_implies_scalar_kg {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator)
    (phi : ContinuumField Point)
    (hStationary : ProjectedMasterStationary integral operator massSq phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact projected_master_stationary_implies_scalar_kg
    (decomposedCandidateMasterAction integral operator)
    (freeScalarRegimeProjection massSq)
    integral operator massSq
    (decomposedScalarSliceExtractionBridge
      integral operator massSq obligations)
    phi hStationary

end
end ConcreteScalarSliceExtraction
end QFT
end ToeFormal
