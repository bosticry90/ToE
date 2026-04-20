# Research Artifact Classification Metadata Schema 2026-04-19 v0

Spec ID:
- `RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the minimum metadata every research-mode artifact must declare.
- Keep equation-level work easy to produce while making its scope, target, and promotability explicit.
- Separate support-only discovery outputs from scientific-delta and sandbox-candidate research outputs.

Required schema tokens:
- `RESEARCH_ARTIFACT_SCHEMA_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `RESEARCH_ARTIFACT_PRIMARY_CLASSES_v0: SUPPORT_ONLY_RESEARCH_ARTIFACT_PLUS_SCIENTIFIC_DELTA_RESEARCH_ARTIFACT_PLUS_SANDBOX_CANDIDATE_RESEARCH_ARTIFACT`
- `RESEARCH_ARTIFACT_METADATA_FIELDS_v0: ARTIFACT_ID_PLUS_RESEARCH_OBJECT_PLUS_RESEARCH_QUESTION_PLUS_TEST_TYPE_PLUS_OUTPUT_KIND_PLUS_TARGET_KIND_PLUS_TARGET_BINDING_PLUS_DELTA_CLASS_PLUS_CONTRADICTION_CONTEXT_PLUS_PROVENANCE_FAMILY_PLUS_NONCLAIM_BOUNDARY_PLUS_PROMOTABILITY`
- `RESEARCH_ARTIFACT_SUPPORT_ONLY_RULE_v0: NO_DELTA_CLASS_OR_NO_TARGET_BINDING_IMPLIES_SUPPORT_ONLY_RESEARCH_ARTIFACT`
- `RESEARCH_ARTIFACT_SCIENTIFIC_DELTA_RULE_v0: DELTA_CLASS_AND_TARGET_BINDING_REQUIRED_FOR_SCIENTIFIC_DELTA_STATUS`
- `RESEARCH_ARTIFACT_SANDBOX_CANDIDATE_RULE_v0: SCIENTIFIC_DELTA_PLUS_CONTRADICTION_CONTEXT_PLUS_READY_FOR_SANDBOX_REVIEW_REQUIRED_FOR_SANDBOX_CANDIDATE_STATUS`
- `RESEARCH_ARTIFACT_GENERATION_DISCIPLINE_v0: METADATA_RECORD_MUST_BE_DECLARED_AT_ARTIFACT_CREATION_TIME`
- `RESEARCH_ARTIFACT_GATE_v0: formal/python/tests/test_research_mode_metadata_schema_gate.py`

Required metadata fields:
- `artifact_id`: stable artifact identifier.
- `research_object`: equation, ansatz, reduction, model, bridge term, or witness package under study.
- `research_question`: the bounded technical question being tested.
- `test_type`: one of `DERIVATION`, `REDUCTION_CHECK`, `SIMULATION`, `COUNTEREXAMPLE_SEARCH`, `NOTATION_REPAIR`, or `DESIGN_ONLY`.
- `output_kind`: one of `DERIVATION_NOTE`, `RESULT_SUMMARY`, `SIMULATION_ARTIFACT`, `COUNTEREXAMPLE`, `RETAIN`, `PRUNE`, or `INCONCLUSIVE`.
- `target_kind`: one of `PILLAR`, `SEAM`, `MASTER_ACTION`, or `NONE`.
- `target_binding`: explicit row, seam, or master-action binding, or `NONE`.
- `delta_class`: explicit scientific delta class or `NONE`.
- `contradiction_context`: declared contradiction check surface or `NONE`.
- `provenance_family`: artifact family, session family, or derivation lineage pointer.
- `nonclaim_boundary`: explicit non-claim statement.
- `promotability`: one of `NOT_READY`, `READY_FOR_SANDBOX_REVIEW`, `READY_FOR_PROMOTION_REVIEW`, or `REJECTED_FROM_PROMOTION`.

Class rules:
- `SUPPORT_ONLY_RESEARCH_ARTIFACT` is the default when no scientific delta class or no explicit target binding exists.
- `SCIENTIFIC_DELTA_RESEARCH_ARTIFACT` requires a declared delta class and explicit target binding but remains research-only until sandbox review.
- `SANDBOX_CANDIDATE_RESEARCH_ARTIFACT` requires scientific delta status, contradiction context, and explicit readiness for sandbox review.

Failure posture:
- Missing metadata fields downgrade the artifact to support-only status.
- A research artifact without contradiction context cannot be sandbox-candidate status.
- Metadata classification does not itself promote the artifact.

Canonical bindings:
- `formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md`
- `formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md`
- `formal/python/tests/test_research_mode_metadata_schema_gate.py`

Non-claim boundary:
- This schema defines repository-local metadata discipline only.
- This schema does not authorize promotion, canonical mutation, or scientific adequacy claims.