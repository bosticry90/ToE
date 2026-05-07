# Repository Artifact Retention Policy 2026-05-05 v0

Spec ID:
- `REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0`

Classification:
- `P-POLICY`

Purpose:
- Keep canonical control-plane artifacts tracked and reviewable.
- Prevent ordinary validation from appending tracked generated output records.
- Freeze new large tracked snapshots by default until an explicit retention or migration packet authorizes them.
- Extend, not replace, `RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0`.

Required policy tokens:
- `REPOSITORY_ARTIFACT_RETENTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `REPOSITORY_ARTIFACT_RETENTION_TRACKED_CANONICAL_v0: SCHEMAS_RELEASE_PACKETS_LEAN_SURFACES_SMALL_SUMMARIES`
- `REPOSITORY_ARTIFACT_RETENTION_GENERATED_OUTPUT_RULE_v0: VERIFY_BY_DEFAULT_WRITE_ONLY_WITH_EXPLICIT_REGEN_AUTHORIZATION`
- `REPOSITORY_ARTIFACT_RETENTION_TRACKED_WRITE_ENV_v0: TOE_ALLOW_TRACKED_OUTPUT_WRITES=1`
- `REPOSITORY_ARTIFACT_RETENTION_LARGE_SNAPSHOT_FREEZE_v0: NO_NEW_LARGE_TRACKED_SNAPSHOTS_BY_DEFAULT`
- `REPOSITORY_ARTIFACT_RETENTION_EXISTING_SNAPSHOT_DISPOSITION_v0: RETAIN_UNTIL_EXPLICIT_MIGRATION_PACKET`
- `REPOSITORY_ARTIFACT_RETENTION_MIGRATION_AUTHORITY_v0: FUTURE_EXPLICIT_PACKET_REQUIRED`
- `REPOSITORY_ARTIFACT_RETENTION_NONCLAIM_BOUNDARY_v0: NO_SCIENTIFIC_AUTHORITY_CHANGE`

Artifact classes:
- `formal/docs/release`: tracked canonical release packets, registries, policies, and small governance artifacts.
- `formal/toe_formal`: tracked Lean authority surfaces.
- `formal/python/tests`: tracked validation gates; ordinary tests must not mutate tracked canonical outputs.
- `formal/python/tools`: tracked tools; generators that write tracked `formal/output` paths must require explicit write authorization.
- `formal/output`: generated or retained outputs; tracked entries are canonical only when explicitly pinned by release packets or gates.
- `formal/tooling_snapshots`: existing large tracked snapshots are retained for history, but new large tracked snapshots are frozen by default.
- `scratch`: temporary workspace material; do not promote to tracked state without an explicit packet.
- `archive`: historical retained material; do not treat as live authority unless a current packet cites it.
- `backup`: historical recovery material; do not treat as live authority unless a current packet cites it.

Write policy:
- Plain `pytest` and governance validation are read-only validation paths.
- Regeneration of tracked `formal/output` artifacts requires an explicit regeneration command and `TOE_ALLOW_TRACKED_OUTPUT_WRITES=1`.
- New large snapshots should be emitted as untracked scratch output, external release artifacts, or a future Git LFS/artifact-storage migration packet.
- Existing large snapshots are not deleted or migrated by this policy.

Canonical bindings:
- `formal/docs/release/READ_ONLY_VALIDATION_HYGIENE_20260505_v0.json`
- `formal/docs/release/ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0.json`
- `formal/docs/release/ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_20260505_v0.json`
- `formal/toe_formal/ToeFormal/Derivation/ArtifactRetentionEnforcementPlan.lean`
- `formal/toe_formal/ToeFormal/Derivation/ArtifactRetentionEnforcementPlanResultReview.lean`
- `formal/python/tools/tracked_output_write_guard.py`
- `formal/python/tests/test_repository_artifact_retention_policy_gate.py`
- `formal/python/tests/test_artifact_retention_enforcement_plan_gate.py`
- `formal/python/tests/test_artifact_retention_enforcement_plan_result_review_gate.py`

Non-claim boundary:
- This policy governs repository-local artifact retention and validation hygiene only.
- This policy does not authorize master-action promotion, pillar completion, seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR source-map closure.
