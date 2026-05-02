/-
ToeFormal/QFT/ToeCandidateFreeScalarWitness.lean

Concrete free-scalar regime witness for the document-level
`TOE_CANDIDATE_MASTER_ACTION_v0` translation surface.

Scope:
- bind the document candidate action inventory to the free-scalar regime reading
- mark scalar kinetic and scalar mass/potential tokens as retained
- mark geometry, fermion, gauge, statistical, transport, retained-unformalized,
  interaction, and seam blocks as explicitly neutralized or inactive in this
  regime
- construct a concrete `DocumentActionDecomposition`
- prove the corresponding `DocumentFreeScalarRegime` witness
- reuse `DocumentMasterActionMapping.lean` to recover the continuum scalar
  quadratic action and KG-class residual conclusion
- no master-action promotion, global ToE claim, seam closure, empirical claim,
  publication packaging, Standard Model/gauge recovery claim, or mechanical
  Markdown parser claim

This is a scalar-regime witness only. It formalizes the bounded free-scalar
reading of the candidate action; it does not claim that the full document-level
master action has been canonically promoted or globally discharged.
-/

import ToeFormal.QFT.ScalarPotentialDecomposition

namespace ToeFormal
namespace QFT
namespace ToeCandidateFreeScalarWitness

open ContinuumFirstVariation
open ScalarSliceExtraction
open DocumentMasterActionMapping
open ScalarPotentialDecomposition
set_option autoImplicit false

noncomputable section

/-- The concrete source tag for this scalar-regime witness. -/
def toeCandidateSourceSpecId : String := sourceSpecId

/-- Stable identifier for the bounded scalar-potential assignment certificate. -/
def toeCandidateScalarPotentialAssignmentCertificateId : String :=
  "TOE_CANDIDATE_MASTER_ACTION_v0_SCALAR_POTENTIAL_ASSIGNMENT_CERTIFICATE_v0"

/-- The bounded scalar-potential assignment certificate keeps its fixed document id. -/
theorem toe_candidate_scalar_potential_assignment_certificate_id_fixed :
    toeCandidateScalarPotentialAssignmentCertificateId =
      "TOE_CANDIDATE_MASTER_ACTION_v0_SCALAR_POTENTIAL_ASSIGNMENT_CERTIFICATE_v0" := by
  rfl

/-- The concrete term inventory used for the `TOE_CANDIDATE_MASTER_ACTION_v0` witness. -/
def toeCandidateDocumentInventory : List DocumentTermToken :=
  documentTermInventory

/-- The witness uses exactly the document inventory from the mapping layer. -/
theorem toe_candidate_inventory_matches_document_inventory :
    toeCandidateDocumentInventory = documentTermInventory := by
  rfl

/-- Free-scalar disposition of each document-level candidate-action token. -/
inductive FreeScalarTokenDisposition where
  | retainedScalarKinetic
  | retainedScalarMass
  | neutralizedNonScalar
  | neutralizedInteraction
  | inactiveSeam
  | neutralizedRetainedUnformalized
deriving DecidableEq, Repr

/-- Explicit token disposition for the bounded free-scalar regime. -/
def toeCandidateFreeScalarDisposition :
    DocumentTermToken → FreeScalarTokenDisposition
  | .geometryEinsteinHilbert => .neutralizedNonScalar
  | .fermionMatter => .neutralizedNonScalar
  | .gaugeField => .neutralizedNonScalar
  | .scalarKinetic => .retainedScalarKinetic
  | .scalarPotentialQuadratic => .retainedScalarMass
  | .scalarInteractionRemainder => .neutralizedInteraction
  | .statisticalEntropy => .neutralizedNonScalar
  | .transportSupport => .neutralizedNonScalar
  | .seamConstraint => .inactiveSeam
  | .retainedUnformalized => .neutralizedRetainedUnformalized

/-- The scalar kinetic and quadratic potential/mass tokens are retained. -/
theorem toe_candidate_scalar_tokens_retained :
    toeCandidateFreeScalarDisposition DocumentTermToken.scalarKinetic =
        FreeScalarTokenDisposition.retainedScalarKinetic ∧
      toeCandidateFreeScalarDisposition
          DocumentTermToken.scalarPotentialQuadratic =
        FreeScalarTokenDisposition.retainedScalarMass := by
  exact ⟨rfl, rfl⟩

/-- Non-scalar document tokens are explicitly neutralized in the free-scalar regime. -/
theorem toe_candidate_primary_non_scalar_tokens_neutralized :
    toeCandidateFreeScalarDisposition
          DocumentTermToken.geometryEinsteinHilbert =
        FreeScalarTokenDisposition.neutralizedNonScalar ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.fermionMatter =
        FreeScalarTokenDisposition.neutralizedNonScalar ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.gaugeField =
        FreeScalarTokenDisposition.neutralizedNonScalar ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.statisticalEntropy =
        FreeScalarTokenDisposition.neutralizedNonScalar ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.transportSupport =
        FreeScalarTokenDisposition.neutralizedNonScalar := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Interaction, seam, and retained-unformalized tokens are exposed separately. -/
theorem toe_candidate_interaction_seam_tokens_neutralized :
    toeCandidateFreeScalarDisposition
          DocumentTermToken.scalarInteractionRemainder =
        FreeScalarTokenDisposition.neutralizedInteraction ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.seamConstraint =
        FreeScalarTokenDisposition.inactiveSeam ∧
      toeCandidateFreeScalarDisposition DocumentTermToken.retainedUnformalized =
        FreeScalarTokenDisposition.neutralizedRetainedUnformalized := by
  exact ⟨rfl, rfl, rfl⟩

/--
Effective mass convention for the scalar quadratic potential in the bounded
free-scalar regime.

The document-level term `-V(phi)` is represented here only by its quadratic
coefficient in the sign convention already used by
`ContinuumFirstVariation.Action`.
-/
def effectiveScalarMassCoeff (massSq : Real) : Real := massSq

/-- The free-scalar mass/potential convention fixes the effective coefficient to `massSq`. -/
theorem effective_scalar_mass_coeff_fixed (massSq : Real) :
    effectiveScalarMassCoeff massSq = massSq := by
  rfl

/-- Explicit scalar-potential split used by the bounded free-scalar witness. -/
def toeCandidateScalarPotential (massSq : Real) : PotentialSplit where
  effectiveQuadraticCoeff := effectiveScalarMassCoeff massSq
  nonlinearRemainder := 0

/-- Structured-source payload for Phase 1 certificate generation. -/
def toeCandidateStructuredScalarPotentialSource (massSq : Real) :
    StructuredScalarPotentialSource where
  sourceSpecId := toeCandidateSourceSpecId
  quadraticToken := DocumentTermToken.scalarPotentialQuadratic
  remainderToken := DocumentTermToken.scalarInteractionRemainder
  effectiveQuadraticCoeff := effectiveScalarMassCoeff massSq
  nonlinearRemainder := 0

/--
Bounded prose-to-structured-source fidelity contract for the scalar-potential
payload used by this witness.

This is not a parser claim. It is an explicit contract object that states which
document-facing identifiers and token classes the machine-facing structured
source is required to match.
-/
structure ProseToStructuredSourceFidelityContract where
  sourceDocumentId : String
  sourceSpecId : String
  quadraticToken : DocumentTermToken
  remainderToken : DocumentTermToken
  quadraticClass : DocumentTermClass
  remainderClass : DocumentTermClass
  noParserClaim : Bool

/-- Concrete bounded contract for `TOE_CANDIDATE_MASTER_ACTION_v0`. -/
def toeCandidateProseToStructuredSourceContractV0 :
    ProseToStructuredSourceFidelityContract where
  sourceDocumentId := "TOE_CANDIDATE_MASTER_ACTION_v0"
  sourceSpecId := toeCandidateSourceSpecId
  quadraticToken := DocumentTermToken.scalarPotentialQuadratic
  remainderToken := DocumentTermToken.scalarInteractionRemainder
  quadraticClass := DocumentTermClass.scalarMass
  remainderClass := DocumentTermClass.interaction
  noParserClaim := true

/--
Contract validity against a chosen structured source.

This theorem surface makes the prose-to-structured-source bridge explicit and
machine-checkable at the token/class contract level.
-/
def ProseToStructuredSourceFidelityContractValid
    (contract : ProseToStructuredSourceFidelityContract)
    (source : StructuredScalarPotentialSource) : Prop :=
  contract.sourceDocumentId = "TOE_CANDIDATE_MASTER_ACTION_v0" ∧
    source.sourceSpecId = contract.sourceSpecId ∧
    source.quadraticToken = contract.quadraticToken ∧
    source.remainderToken = contract.remainderToken ∧
    classifyDocumentTerm source.quadraticToken = contract.quadraticClass ∧
    classifyDocumentTerm source.remainderToken = contract.remainderClass ∧
    contract.noParserClaim = true

/-- The concrete contract remains explicitly non-parser and source-id pinned. -/
theorem toe_candidate_prose_to_structured_source_contract_id_and_boundary :
    toeCandidateProseToStructuredSourceContractV0.sourceDocumentId =
        "TOE_CANDIDATE_MASTER_ACTION_v0" ∧
      toeCandidateProseToStructuredSourceContractV0.sourceSpecId =
        toeCandidateSourceSpecId ∧
      toeCandidateProseToStructuredSourceContractV0.noParserClaim = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- The structured source satisfies the bounded prose-to-structured-source contract. -/
theorem toe_candidate_structured_source_satisfies_prose_contract
    (massSq : Real) :
    ProseToStructuredSourceFidelityContractValid
      toeCandidateProseToStructuredSourceContractV0
      (toeCandidateStructuredScalarPotentialSource massSq) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The structured-source payload satisfies the bounded free-scalar token contract. -/
theorem toe_candidate_structured_scalar_potential_source_valid
    (massSq : Real) :
    StructuredScalarPotentialSourceValid
      (toeCandidateStructuredScalarPotentialSource massSq) := by
  exact ⟨rfl, rfl⟩

/--
Concrete bounded certificate for how `TOE_CANDIDATE_MASTER_ACTION_v0` supplies
the scalar-potential assignment used by this witness.
-/
def toeCandidateScalarPotentialAssignmentCertificateV0 (massSq : Real) :
    ScalarPotentialAssignmentCertificate :=
  certificateFromStructuredSource
    (toeCandidateStructuredScalarPotentialSource massSq)

/-- The bounded scalar-potential certificate is valid for the selected split. -/
theorem toe_candidate_scalar_potential_assignment_certificate_valid
    (massSq : Real) :
    ScalarPotentialAssignmentCertificateValid
      (toeCandidateScalarPotentialAssignmentCertificateV0 massSq) := by
  exact certificate_from_structured_source_valid
    (toeCandidateStructuredScalarPotentialSource massSq)
    (toe_candidate_structured_scalar_potential_source_valid massSq)

/--
Concrete document-level assignment from the scalar-potential tokens in
`TOE_CANDIDATE_MASTER_ACTION_v0` to the potential split used by this witness.
-/
def toeCandidateDocumentPotentialAssignment (massSq : Real) :
    DocumentPotentialAssignment :=
  certificateGeneratedAssignment
    (toeCandidateScalarPotentialAssignmentCertificateV0 massSq)

/-- The bounded certificate generates the current document potential assignment. -/
theorem toe_candidate_scalar_potential_assignment_certificate_generates_assignment
    (massSq : Real) :
    certificateGeneratedAssignment
        (toeCandidateScalarPotentialAssignmentCertificateV0 massSq) =
      toeCandidateDocumentPotentialAssignment massSq := by
  rfl

/--
Bounded audit gate for document-to-certificate fidelity in the scalar lane.

This gate is not a parser and does not promote the master action. It records
the exact machine-facing checks required for the current bounded route.
-/
structure ScalarPotentialCertificateAuditGate where
  certificateId : String
  certificate : ScalarPotentialAssignmentCertificate
  noMasterActionPromotionClaim : Bool
  noGlobalActionClaim : Bool

/--
Structured source for audit-gate field coverage in the bounded scalar route.

This extends the structured-source pattern beyond certificate construction by
making the audit-gate control fields explicit machine-facing inputs.
-/
structure StructuredScalarPotentialAuditSource where
  certificateId : String
  sourcePayload : StructuredScalarPotentialSource
  noMasterActionPromotionClaim : Bool
  noGlobalActionClaim : Bool
  expectedRemainderDisposition : FreeScalarTokenDisposition
  expectedSeamDisposition : FreeScalarTokenDisposition

/-- Validity contract for structured audit-source coverage. -/
def StructuredScalarPotentialAuditSourceValid
    (source : StructuredScalarPotentialAuditSource) : Prop :=
  source.certificateId = toeCandidateScalarPotentialAssignmentCertificateId ∧
    StructuredScalarPotentialSourceValid source.sourcePayload ∧
    source.sourcePayload.sourceSpecId = toeCandidateSourceSpecId ∧
    source.noMasterActionPromotionClaim = false ∧
    source.noGlobalActionClaim = false ∧
    source.expectedRemainderDisposition =
      FreeScalarTokenDisposition.neutralizedInteraction ∧
    source.expectedSeamDisposition = FreeScalarTokenDisposition.inactiveSeam

/-- Concrete structured audit source for the bounded scalar witness. -/
def toeCandidateStructuredScalarPotentialAuditSource (massSq : Real) :
    StructuredScalarPotentialAuditSource where
  certificateId := toeCandidateScalarPotentialAssignmentCertificateId
  sourcePayload := toeCandidateStructuredScalarPotentialSource massSq
  noMasterActionPromotionClaim := false
  noGlobalActionClaim := false
  expectedRemainderDisposition := FreeScalarTokenDisposition.neutralizedInteraction
  expectedSeamDisposition := FreeScalarTokenDisposition.inactiveSeam

/-- The concrete structured audit source satisfies the bounded coverage contract. -/
theorem toe_candidate_structured_scalar_potential_audit_source_valid
    (massSq : Real) :
    StructuredScalarPotentialAuditSourceValid
      (toeCandidateStructuredScalarPotentialAuditSource massSq) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact toe_candidate_structured_scalar_potential_source_valid massSq

/--
Validity conditions for the bounded scalar-potential certificate audit gate.

Checks enforced here:
- expected certificate id
- expected source document id
- expected quadratic/remainder tokens
- expected quadratic/remainder classes
- expected free-scalar neutralization status
- explicit no-promotion/no-global-claim boundary flags
-/
def ScalarPotentialCertificateAuditGateValid
    (gate : ScalarPotentialCertificateAuditGate) : Prop :=
  gate.certificateId =
      toeCandidateScalarPotentialAssignmentCertificateId ∧
    gate.certificate.sourceSpecId = toeCandidateSourceSpecId ∧
    gate.certificate.quadraticToken =
      DocumentTermToken.scalarPotentialQuadratic ∧
    gate.certificate.remainderToken =
      DocumentTermToken.scalarInteractionRemainder ∧
    gate.certificate.quadraticClass = DocumentTermClass.scalarMass ∧
    gate.certificate.remainderClass = DocumentTermClass.interaction ∧
    toeCandidateFreeScalarDisposition gate.certificate.remainderToken =
      FreeScalarTokenDisposition.neutralizedInteraction ∧
    toeCandidateFreeScalarDisposition DocumentTermToken.seamConstraint =
      FreeScalarTokenDisposition.inactiveSeam ∧
    gate.noMasterActionPromotionClaim = false ∧
    gate.noGlobalActionClaim = false ∧
    ScalarPotentialAssignmentCertificateValid gate.certificate

/--
Concrete bounded audit gate for
`TOE_CANDIDATE_MASTER_ACTION_v0_SCALAR_POTENTIAL_ASSIGNMENT_CERTIFICATE_v0`.
-/
def toeCandidateScalarPotentialAssignmentAuditGateV0 (massSq : Real) :
    ScalarPotentialCertificateAuditGate :=
  let source := toeCandidateStructuredScalarPotentialAuditSource massSq
  { certificateId := source.certificateId
    certificate := certificateFromStructuredSource source.sourcePayload
    noMasterActionPromotionClaim := source.noMasterActionPromotionClaim
    noGlobalActionClaim := source.noGlobalActionClaim }

/--
The concrete bounded document-to-certificate audit gate is valid.
-/
theorem toe_candidate_scalar_potential_assignment_audit_gate_valid
    (massSq : Real) :
    ScalarPotentialCertificateAuditGateValid
      (toeCandidateScalarPotentialAssignmentAuditGateV0 massSq) := by
  have hSource : StructuredScalarPotentialAuditSourceValid
    (toeCandidateStructuredScalarPotentialAuditSource massSq) :=
  toe_candidate_structured_scalar_potential_audit_source_valid massSq
  rcases hSource with
  ⟨hCertId, hPayloadValid, hSourceSpecId, hNoPromotion, hNoGlobal,
    hRemainderDisposition, hSeamDisposition⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hCertId
  · simpa [toeCandidateScalarPotentialAssignmentAuditGateV0,
    toeCandidateStructuredScalarPotentialAuditSource] using hSourceSpecId
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hNoPromotion
  · exact hNoGlobal
  · simpa [toeCandidateScalarPotentialAssignmentAuditGateV0,
    toeCandidateStructuredScalarPotentialAuditSource]
    using (certificate_from_structured_source_valid
    (toeCandidateStructuredScalarPotentialSource massSq)
    (toe_candidate_structured_scalar_potential_source_valid massSq))

/--
The bounded free-scalar witness maps the document scalar-potential tokens to the
explicit potential split it uses.
-/
theorem toe_candidate_scalar_potential_tokens_map_to_split (massSq : Real) :
    (toeCandidateDocumentPotentialAssignment massSq).quadraticToken =
        DocumentTermToken.scalarPotentialQuadratic ∧
      (toeCandidateDocumentPotentialAssignment massSq).remainderToken =
        DocumentTermToken.scalarInteractionRemainder ∧
      (toeCandidateDocumentPotentialAssignment massSq).split =
        toeCandidateScalarPotential massSq := by
  exact ⟨rfl, rfl, rfl⟩

/-- The selected scalar-potential tokens have the expected document classes. -/
theorem toe_candidate_document_potential_assignment_valid (massSq : Real) :
    DocumentPotentialAssignmentValid
      (toeCandidateDocumentPotentialAssignment massSq) := by
  exact valid_certificate_generates_valid_assignment
    (toeCandidateScalarPotentialAssignmentCertificateV0 massSq)
    (toe_candidate_scalar_potential_assignment_certificate_valid massSq)

/-- The bounded scalar witness uses the quadratic free-scalar potential regime. -/
theorem toe_candidate_scalar_potential_quadratic_regime (massSq : Real) :
    QuadraticFreeScalarRegime (toeCandidateScalarPotential massSq) massSq := by
  exact ⟨effective_scalar_mass_coeff_fixed massSq, rfl⟩

/-- The document-level potential assignment inherits the same quadratic regime. -/
theorem toe_candidate_document_potential_assignment_quadratic_regime
    (massSq : Real) :
    QuadraticFreeScalarRegime
      (toeCandidateDocumentPotentialAssignment massSq).split massSq := by
  simpa [toeCandidateDocumentPotentialAssignment] using
    toe_candidate_scalar_potential_quadratic_regime massSq

/-- The scalar-potential split exposes the chosen mass coefficient and zero remainder. -/
theorem toe_candidate_scalar_potential_split_coefficients (massSq : Real) :
    (toeCandidateScalarPotential massSq).effectiveQuadraticCoeff = massSq ∧
      (toeCandidateScalarPotential massSq).nonlinearRemainder = 0 := by
  exact toe_candidate_scalar_potential_quadratic_regime massSq

/-- In the quadratic free-scalar regime, the document potential reduces to the scalar mass term. -/
theorem toe_candidate_scalar_potential_reduces_to_mass_term {Point : Type}
    (integral : ContinuumField Point → Real)
    (phi : ContinuumField Point)
    (massSq : Real) :
    scalarPotentialContribution integral phi (toeCandidateScalarPotential massSq) =
      (1 / 2 : Real) * massSq * ContinuumPair integral phi phi := by
  exact quadratic_regime_reduces_to_mass_term
    integral phi (toeCandidateScalarPotential massSq) massSq
    (toe_candidate_scalar_potential_quadratic_regime massSq)

/--
Concrete document decomposition for the `TOE_CANDIDATE_MASTER_ACTION_v0`
free-scalar regime.

All excluded blocks are set to zero because this is the free-scalar regime
selection. Those zeros are not global claims about the candidate action; they
are the explicit regime assumptions recorded by the witness below.
-/
def toeCandidateFreeScalarDecomposition {Point : Type}
    (phi : ContinuumField Point)
    (massSq : Real) :
    DocumentActionDecomposition Point :=
  documentPotentialAssignmentDecomposition phi
    (toeCandidateDocumentPotentialAssignment massSq)

/-- Scalar coefficient choices in the concrete free-scalar document decomposition. -/
theorem toe_candidate_free_scalar_coefficients {Point : Type}
    (phi : ContinuumField Point)
    (massSq : Real) :
    (toeCandidateFreeScalarDecomposition phi massSq).scalarKineticCoeff = 1 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).scalarMassCoeff =
        massSq := by
  exact ⟨rfl, (toe_candidate_scalar_potential_split_coefficients massSq).1⟩

/-- All excluded document blocks are neutralized in the concrete free-scalar decomposition. -/
theorem toe_candidate_free_scalar_excluded_blocks_zero {Point : Type}
    (phi : ContinuumField Point)
    (massSq : Real) :
    (toeCandidateFreeScalarDecomposition phi massSq).geometryBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).fermionMatterBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).gaugeBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).statisticalEntropyBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).transportSupportBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).retainedUnformalizedBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).scalarInteractionBlock = 0 ∧
      (toeCandidateFreeScalarDecomposition phi massSq).seamConstraintBlock = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    (toe_candidate_scalar_potential_split_coefficients massSq).2, rfl⟩

/--
Concrete `DocumentFreeScalarRegime` witness for the bounded free-scalar reading
of `TOE_CANDIDATE_MASTER_ACTION_v0`.
-/
theorem toe_candidate_free_scalar_regime_witness {Point : Type}
    (phi : ContinuumField Point)
    (massSq : Real) :
    DocumentFreeScalarRegime
      (toeCandidateFreeScalarDecomposition phi massSq) phi massSq := by
  unfold toeCandidateFreeScalarDecomposition
  exact quadratic_regime_yields_document_free_scalar_regime
    phi (toeCandidateDocumentPotentialAssignment massSq).split massSq
    (toe_candidate_document_potential_assignment_quadratic_regime massSq)

/--
The concrete `TOE_CANDIDATE_MASTER_ACTION_v0` free-scalar witness reduces the
document action to the continuum scalar quadratic action.
-/
theorem toe_candidate_free_scalar_action_reduces_to_scalar {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (phi : ContinuumField Point)
    (massSq : Real) :
    DocumentCandidateAction integral operator
        (toeCandidateFreeScalarDecomposition phi massSq) =
      ContinuumFirstVariation.Action integral operator massSq phi := by
  exact document_free_scalar_action_reduces_to_scalar
    integral operator
    (toeCandidateFreeScalarDecomposition phi massSq)
    phi massSq
    (toe_candidate_free_scalar_regime_witness phi massSq)

/--
With the concrete free-scalar document witness supplied, projected scalar
stationarity implies the continuum KG-class residual equation.
-/
theorem toe_candidate_free_scalar_stationary_implies_kg {Point : Type}
    (integral : ContinuumField Point → Real)
    (operator : ContinuumField Point → ContinuumField Point)
    (phi : ContinuumField Point)
    (massSq : Real)
    (obligations : ContinuumFirstVariationObligations integral operator)
    (hStationary : ProjectedMasterStationary integral operator massSq phi) :
    ResidualEquation (Residual operator massSq phi) := by
  exact document_mapped_stationary_implies_scalar_kg
    integral operator
    (toeCandidateFreeScalarDecomposition phi massSq)
    phi massSq obligations
    (toe_candidate_free_scalar_regime_witness phi massSq)
    hStationary

end
end ToeCandidateFreeScalarWitness
end QFT
end ToeFormal
