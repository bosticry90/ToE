# Derivation Target: GR Empirical Discriminator EMP-GR-01 v0

Spec ID:
- `DERIVATION_TARGET_GR_EMPIRICAL_DISCRIMINATOR_EMP_GR_01_v0`

Target ID:
- `TARGET-GR-EMPIRICAL-DISCRIMINATOR-EMP-GR-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one bounded, non-claim discriminator package for the GR lane.
- Establish a machine-checkable bridge from artifact to elimination-facing decision posture.

Non-claim boundary:
- bounded discriminator run package.
- no external truth claim.
- no automatic adjudication promotion.

Discriminator status token:
- `EMP_GR_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`

Artifact bundle:
- `EMP_GR_01_ARTIFACT_v0: gr_empirical_discriminator_emp_gr_01_run_cycle01_v0`
- `EMP_GR_01_ARTIFACT_SHA256_v0: 328f19c298461f0dcd82f234b5bdcbb12dace9081f5809cd4a707c8b1c794f3e`
- `EMP_GR_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/gr_empirical_discriminator_emp_gr_01_run_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_gr_empirical_discriminator_emp_gr_01_scaffold_gate.py`

Run semantics:
- `EMP_GR_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
- `EMP_GR_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
- pass/fail outcome is bounded to the declared lane and candidate scope in the run artifact.

Execution lane pointers:
- derivation lane policy pointer:
  - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
- bridge evidence lane pointer:
  - `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md`

Scope statement:
- this target pins one bounded discriminator run for GR with explicit pass/fail prune semantics.
- it does not assert that GR is empirically validated.
