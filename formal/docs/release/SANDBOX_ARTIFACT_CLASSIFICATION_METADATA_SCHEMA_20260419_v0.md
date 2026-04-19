# Sandbox Artifact Classification Metadata Schema 2026-04-19 v0

Spec ID:
- `SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the minimum classification and metadata surface every sandbox artifact must declare.
- Separate support-only exploratory outputs from scientific-delta artifacts and promotion-candidate artifacts.
- Make promotion eligibility fail closed at metadata time rather than only at late governance review.

Required schema tokens:
- `SANDBOX_ARTIFACT_CLASSIFICATION_SCHEMA_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `SANDBOX_ARTIFACT_CLASSIFICATION_PRIMARY_CLASSES_v0: SUPPORT_ONLY_SANDBOX_ARTIFACT_PLUS_SCIENTIFIC_DELTA_SANDBOX_ARTIFACT_PLUS_PROMOTION_CANDIDATE_SANDBOX_ARTIFACT`
- `SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_FIELDS_v0: ARTIFACT_ID_PLUS_ARTIFACT_CLASS_PLUS_DELTA_CLASS_PLUS_PROVENANCE_FAMILY_PLUS_DECLARED_SCOPE_PLUS_TARGET_BINDING_PLUS_CONTRADICTION_CHECK_PLUS_NONCLAIM_BOUNDARY_PLUS_PROMOTION_READINESS`
- `SANDBOX_ARTIFACT_CLASSIFICATION_SUPPORT_ONLY_RULE_v0: NO_DELTA_CLASS_OR_NO_TARGET_BINDING_IMPLIES_SUPPORT_ONLY_NONPROMOTABLE`
- `SANDBOX_ARTIFACT_CLASSIFICATION_SCIENTIFIC_DELTA_RULE_v0: DELTA_CLASS_AND_TARGET_BINDING_REQUIRED_FOR_SCIENTIFIC_DELTA_STATUS`
- `SANDBOX_ARTIFACT_CLASSIFICATION_PROMOTION_CANDIDATE_RULE_v0: SCIENTIFIC_DELTA_PLUS_CONTRADICTION_CHECK_PLUS_PROMOTION_READINESS_REQUIRED_FOR_PROMOTION_CANDIDATE_STATUS`
- `SANDBOX_ARTIFACT_CLASSIFICATION_GENERATION_DISCIPLINE_v0: METADATA_RECORD_MUST_BE_DECLARED_AT_ARTIFACT_CREATION_TIME`
- `SANDBOX_ARTIFACT_CLASSIFICATION_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py`

Required metadata fields:
- `artifact_id`: stable artifact identifier.
- `artifact_class`: one of `SUPPORT_ONLY_SANDBOX_ARTIFACT`, `SCIENTIFIC_DELTA_SANDBOX_ARTIFACT`, or `PROMOTION_CANDIDATE_SANDBOX_ARTIFACT`.
- `delta_class`: explicit scientific delta class or `NONE`.
- `provenance_family`: artifact family, tranche, or derivation lineage pointer.
- `declared_scope`: bounded row, seam, or pillar scope.
- `target_binding`: explicit target row or target seam reference.
- `contradiction_check`: declared contradiction check surface and result.
- `nonclaim_boundary`: explicit non-claim statement.
- `promotion_readiness`: `NOT_READY`, `READY_FOR_PROMOTION_REVIEW`, or `REJECTED_FROM_PROMOTION`.

Class rules:
- `SUPPORT_ONLY_SANDBOX_ARTIFACT` is the default when no scientific delta class or no explicit target binding exists.
- `SCIENTIFIC_DELTA_SANDBOX_ARTIFACT` requires a declared delta class and explicit target binding but remains sandbox-only until promotion review.
- `PROMOTION_CANDIDATE_SANDBOX_ARTIFACT` requires scientific delta status plus contradiction evidence and explicit promotion readiness.

Failure posture:
- Missing metadata fields downgrade the artifact to support-only status.
- A sandbox artifact without contradiction context cannot be promotion-candidate status.
- Metadata classification does not itself promote the artifact.

Canonical bindings:
- `formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md`
- `formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json`
- `formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py`

Non-claim boundary:
- This schema defines repository-local metadata discipline only.
- This schema does not authorize promotion, canonical mutation, or scientific adequacy claims.