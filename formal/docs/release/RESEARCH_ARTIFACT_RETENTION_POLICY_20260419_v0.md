# Research Artifact Retention Policy 2026-04-19 v0

Spec ID:
- `RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0`

Classification:
- `P-POLICY`

Purpose:
- Preserve useful research outputs even when they are negative, inconclusive, or non-promotable.
- Prevent the loss of failed derivations, counterexamples, and pruned hypotheses that still reduce future search space.
- Keep research retention separate from canonical state mirrors.

Required policy tokens:
- `RESEARCH_ARTIFACT_RETENTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `RESEARCH_ARTIFACT_RETENTION_ALLOWED_OUTCOMES_v0: RETAIN_PRUNE_INCONCLUSIVE_COUNTEREXAMPLE_AND_DESIGN_ONLY`
- `RESEARCH_ARTIFACT_RETENTION_ARCHIVE_ROOT_v0: formal/output/research_archive`
- `RESEARCH_ARTIFACT_RETENTION_INDEX_ROOT_v0: formal/python/research`
- `RESEARCH_ARTIFACT_RETENTION_CANONICAL_RULE_v0: NO_STATE_OF_THE_THEORY_MIRROR_BY_DEFAULT`
- `RESEARCH_ARTIFACT_RETENTION_ESCALATION_RULE_v0: EXPLICIT_SANDBOX_REVIEW_REQUIRED_BEFORE_PROMOTION_PACKAGING`
- `RESEARCH_ARTIFACT_RETENTION_GATE_v0: formal/python/tests/test_research_mode_lane_policy_gate.py`

Retention rules:
- Negative mathematical results are first-class research outputs and must not be discarded solely because they are non-promotable.
- Research artifacts may be archived even when they are support-only.
- Canonical mirrors remain opt-in and promotion-gated.

Canonical bindings:
- `formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/python/tests/test_research_mode_lane_policy_gate.py`

Non-claim boundary:
- This policy governs repository-local research retention only.
- This policy does not authorize canonical mutation or external scientific claims.