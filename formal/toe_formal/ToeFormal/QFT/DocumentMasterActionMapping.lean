/-
ToeFormal/QFT/DocumentMasterActionMapping.lean

Lean-side translation layer from the document-level candidate master action
surface to the decomposed scalar-slice formal surface.

Scope:
- inventory the `TOE_CANDIDATE_MASTER_ACTION_v0` term classes used by the
  bounded free-scalar route
- define a document-action decomposition object and an explicit translation
  into `DecomposedMasterConfig`
- prove that the translated document decomposition instantiates
  `DecomposedCandidateAction`
- prove that the free-scalar document regime maps to the concrete scalar
  projection used by `ConcreteScalarSliceExtraction.lean`
- no canonical master-action promotion, global ToE claim, seam closure,
  empirical claim, publication packaging, gauge/Standard Model recovery claim,
  or claim that the markdown document has been mechanically parsed

The remaining blocker is outside this file: justify that the prose/math object
in `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md` is faithfully captured
by a value of `DocumentActionDecomposition` with the stated free-scalar regime
witness.
-/

import ToeFormal.QFT.ConcreteScalarSliceExtraction

namespace ToeFormal
namespace QFT
namespace DocumentMasterActionMapping

open ContinuumFirstVariation
open ConcreteScalarSliceExtraction
open ScalarSliceExtraction
set_option autoImplicit false

noncomputable section

/-- The document-level source whose free-scalar translation is being modeled. -/
def sourceSpecId : String := "TOE_CANDIDATE_MASTER_ACTION_v0"

/-- Coarse classes needed for the strict free-scalar translation target. -/
inductive DocumentTermClass where
  | scalarKinetic
  | scalarMass
  | nonScalar
  | interaction
  | seamCoupling
  | retainedNotFormalized
deriving DecidableEq, Repr

/--
Document-level term tokens from the candidate master-action surface, at the
classification granularity needed by the scalar slice.
-/
inductive DocumentTermToken where
  | geometryEinsteinHilbert
  | fermionMatter
  | gaugeField
  | scalarKinetic
  | scalarPotentialQuadratic
  | scalarInteractionRemainder
  | statisticalEntropy
  | transportSupport
  | seamConstraint
  | retainedUnformalized
deriving DecidableEq, Repr

/-- Classification of document terms into the decomposed scalar-slice blocks. -/
def classifyDocumentTerm : DocumentTermToken → DocumentTermClass
  | .geometryEinsteinHilbert => .nonScalar
  | .fermionMatter => .nonScalar
  | .gaugeField => .nonScalar
  | .scalarKinetic => .scalarKinetic
  | .scalarPotentialQuadratic => .scalarMass
  | .scalarInteractionRemainder => .interaction
  | .statisticalEntropy => .nonScalar
  | .transportSupport => .nonScalar
  | .seamConstraint => .seamCoupling
  | .retainedUnformalized => .retainedNotFormalized

/-- The candidate action term inventory used by this bounded mapping surface. -/
def documentTermInventory : List DocumentTermToken :=
  [ DocumentTermToken.geometryEinsteinHilbert
  , DocumentTermToken.fermionMatter
  , DocumentTermToken.gaugeField
  , DocumentTermToken.scalarKinetic
  , DocumentTermToken.scalarPotentialQuadratic
  , DocumentTermToken.scalarInteractionRemainder
  , DocumentTermToken.statisticalEntropy
  , DocumentTermToken.transportSupport
  , DocumentTermToken.seamConstraint
  , DocumentTermToken.retainedUnformalized
  ]

/-- Scalar kinetic term is mapped to the scalar kinetic coefficient block. -/
theorem scalar_kinetic_classified :
    classifyDocumentTerm DocumentTermToken.scalarKinetic =
      DocumentTermClass.scalarKinetic := by
  rfl

/-- Quadratic scalar potential contribution is mapped to the scalar mass block. -/
theorem scalar_potential_quadratic_classified :
    classifyDocumentTerm DocumentTermToken.scalarPotentialQuadratic =
      DocumentTermClass.scalarMass := by
  rfl

/-- Geometry, matter, gauge, statistical, and transport tokens are non-scalar blocks. -/
theorem primary_non_scalar_terms_classified :
    classifyDocumentTerm DocumentTermToken.geometryEinsteinHilbert =
        DocumentTermClass.nonScalar ∧
      classifyDocumentTerm DocumentTermToken.fermionMatter =
        DocumentTermClass.nonScalar ∧
      classifyDocumentTerm DocumentTermToken.gaugeField =
        DocumentTermClass.nonScalar ∧
      classifyDocumentTerm DocumentTermToken.statisticalEntropy =
        DocumentTermClass.nonScalar ∧
      classifyDocumentTerm DocumentTermToken.transportSupport =
        DocumentTermClass.nonScalar := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Seam-constraint tokens are mapped to the seam/coupling block. -/
theorem seam_constraint_classified :
    classifyDocumentTerm DocumentTermToken.seamConstraint =
      DocumentTermClass.seamCoupling := by
  rfl

/--
Document-level decomposition of the candidate master action at the exact
granularity needed to instantiate `DecomposedMasterConfig`.

`scalarMassCoeff` is the effective quadratic coefficient of the scalar
potential in the sign convention used by `ContinuumFirstVariation.Action`.
-/
structure DocumentActionDecomposition (Point : Type) where
  scalarField : ContinuumField Point
  scalarKineticCoeff : Real
  scalarMassCoeff : Real
  geometryBlock : Real
  fermionMatterBlock : Real
  gaugeBlock : Real
  statisticalEntropyBlock : Real
  transportSupportBlock : Real
  retainedUnformalizedBlock : Real
  scalarInteractionBlock : Real
  seamConstraintBlock : Real

/-- Aggregate of document terms that are non-scalar in the free-scalar slice. -/
def nonScalarAggregate {Point : Type}
    (doc : DocumentActionDecomposition Point) : Real :=
  doc.geometryBlock + doc.fermionMatterBlock + doc.gaugeBlock +
    doc.statisticalEntropyBlock + doc.transportSupportBlock +
    doc.retainedUnformalizedBlock

/-- Translation from document decomposition into the decomposed formal surface. -/
def documentToDecomposedConfig {Point : Type}
    (doc : DocumentActionDecomposition Point) :
    DecomposedMasterConfig Point where
  scalarField := doc.scalarField
  kineticCoeff := doc.scalarKineticCoeff
  massCoeff := doc.scalarMassCoeff
  nonScalarBlock := nonScalarAggregate doc
  interactionBlock := doc.scalarInteractionBlock
  seamBlock := doc.seamConstraintBlock

/-- Direct formal action associated with the document-level decomposition. -/
def DocumentCandidateAction {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (doc : DocumentActionDecomposition Point) : Real :=
  (1 / 2 : Real) * doc.scalarKineticCoeff *
      ContinuumPair integral doc.scalarField (operator doc.scalarField) +
    (1 / 2 : Real) * doc.scalarMassCoeff *
      ContinuumPair integral doc.scalarField doc.scalarField +
    nonScalarAggregate doc + doc.scalarInteractionBlock +
      doc.seamConstraintBlock

/-- Fieldwise equality principle for the decomposed scalar-slice config. -/
theorem decomposed_config_eq_of_fields {Point : Type}
    {x y : DecomposedMasterConfig Point}
    (hScalar : x.scalarField = y.scalarField)
    (hKinetic : x.kineticCoeff = y.kineticCoeff)
    (hMass : x.massCoeff = y.massCoeff)
    (hNonScalar : x.nonScalarBlock = y.nonScalarBlock)
    (hInteraction : x.interactionBlock = y.interactionBlock)
    (hSeam : x.seamBlock = y.seamBlock) :
    x = y := by
  cases x with
  | mk xScalar xKinetic xMass xNonScalar xInteraction xSeam =>
    cases y with
    | mk yScalar yKinetic yMass yNonScalar yInteraction ySeam =>
      change xScalar = yScalar at hScalar
      change xKinetic = yKinetic at hKinetic
      change xMass = yMass at hMass
      change xNonScalar = yNonScalar at hNonScalar
      change xInteraction = yInteraction at hInteraction
      change xSeam = ySeam at hSeam
      cases hScalar
      cases hKinetic
      cases hMass
      cases hNonScalar
      cases hInteraction
      cases hSeam
      rfl

/--
Mapping theorem: the document decomposition instantiates the decomposed formal
candidate-action surface.
-/
theorem document_action_maps_to_decomposed_candidate_action {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (doc : DocumentActionDecomposition Point) :
    DocumentCandidateAction integral operator doc =
      DecomposedCandidateAction integral operator
        (documentToDecomposedConfig doc) := by
  unfold DocumentCandidateAction DecomposedCandidateAction documentToDecomposedConfig
  ring

/--
Document-level free-scalar regime assumptions.

These are not global claims about the candidate master action. They are the
local translation hypotheses needed to map the document surface into the
already-proved decomposed scalar slice.
-/
structure DocumentFreeScalarRegime {Point : Type}
    (doc : DocumentActionDecomposition Point)
    (phi : ContinuumField Point)
    (massSq : Real) where
  scalar_selected : doc.scalarField = phi
  kinetic_fixed : doc.scalarKineticCoeff = 1
  mass_fixed : doc.scalarMassCoeff = massSq
  geometry_neutral : doc.geometryBlock = 0
  fermion_matter_neutral : doc.fermionMatterBlock = 0
  gauge_neutral : doc.gaugeBlock = 0
  statistical_entropy_neutral : doc.statisticalEntropyBlock = 0
  transport_support_neutral : doc.transportSupportBlock = 0
  retained_unformalized_neutral : doc.retainedUnformalizedBlock = 0
  scalar_interaction_zero : doc.scalarInteractionBlock = 0
  seam_constraint_inactive : doc.seamConstraintBlock = 0

/--
The free-scalar document regime maps exactly to the concrete decomposed
free-scalar embedding.
-/
theorem document_free_scalar_regime_maps_to_free_scalar_embed {Point : Type}
    (doc : DocumentActionDecomposition Point)
    (phi : ContinuumField Point)
    (massSq : Real)
    (hRegime : DocumentFreeScalarRegime doc phi massSq) :
    documentToDecomposedConfig doc = freeScalarEmbed massSq phi := by
  apply decomposed_config_eq_of_fields
  · exact hRegime.scalar_selected
  · exact hRegime.kinetic_fixed
  · exact hRegime.mass_fixed
  · unfold documentToDecomposedConfig freeScalarEmbed nonScalarAggregate
    rw [hRegime.geometry_neutral, hRegime.fermion_matter_neutral,
      hRegime.gauge_neutral, hRegime.statistical_entropy_neutral,
      hRegime.transport_support_neutral, hRegime.retained_unformalized_neutral]
    ring
  · exact hRegime.scalar_interaction_zero
  · exact hRegime.seam_constraint_inactive

/--
Under the document free-scalar regime, the document action maps to the formal
decomposed free-scalar action.
-/
theorem document_free_scalar_action_maps_to_decomposed_action {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (doc : DocumentActionDecomposition Point)
    (phi : ContinuumField Point)
    (massSq : Real)
    (hRegime : DocumentFreeScalarRegime doc phi massSq) :
    DocumentCandidateAction integral operator doc =
      DecomposedCandidateAction integral operator (freeScalarEmbed massSq phi) := by
  rw [document_action_maps_to_decomposed_candidate_action]
  rw [document_free_scalar_regime_maps_to_free_scalar_embed doc phi massSq hRegime]

/--
Document-to-scalar theorem: once the document decomposition and free-scalar
regime hypotheses are supplied, the document action reduces to the continuum
scalar quadratic action.
-/
theorem document_free_scalar_action_reduces_to_scalar {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (doc : DocumentActionDecomposition Point)
    (phi : ContinuumField Point)
    (massSq : Real)
    (hRegime : DocumentFreeScalarRegime doc phi massSq) :
    DocumentCandidateAction integral operator doc =
      ContinuumFirstVariation.Action integral operator massSq phi := by
  rw [document_free_scalar_action_maps_to_decomposed_action
    integral operator doc phi massSq hRegime]
  exact decomposed_action_reduces_to_scalar integral operator massSq phi

/--
Document-to-KG reuse theorem: with the document translation supplied and the
already explicit continuum obligations, projected scalar stationarity gives the
KG-class residual equation. The document mapping is used to expose the scalar
action reduction; the KG conclusion remains the same bounded decomposed-slice
theorem.
-/
theorem document_mapped_stationary_implies_scalar_kg {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (doc : DocumentActionDecomposition Point)
    (phi : ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator)
    (hRegime : DocumentFreeScalarRegime doc phi massSq)
    (hStationary : ProjectedMasterStationary integral operator massSq phi) :
    ResidualEquation (Residual operator massSq phi) := by
  have _hReduction :
      DocumentCandidateAction integral operator doc =
        ContinuumFirstVariation.Action integral operator massSq phi :=
    document_free_scalar_action_reduces_to_scalar
      integral operator doc phi massSq hRegime
  exact decomposed_projected_master_stationary_implies_scalar_kg
    integral operator massSq obligations phi hStationary

end
end DocumentMasterActionMapping
end QFT
end ToeFormal
