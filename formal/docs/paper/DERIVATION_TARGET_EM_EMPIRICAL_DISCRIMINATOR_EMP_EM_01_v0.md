# Derivation Target: EM Empirical Discriminator EMP-EM-01 v0

Spec ID:
- `DERIVATION_TARGET_EM_EMPIRICAL_DISCRIMINATOR_EMP_EM_01_v0`

Target ID:
- `TARGET-EM-EMPIRICAL-DISCRIMINATOR-EMP-EM-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one bounded, non-claim discriminator package for the EM lane.
- Establish a machine-checkable bridge from artifact to elimination-facing decision posture.

Non-claim boundary:
- bounded discriminator run package.
- no external truth claim.
- no automatic adjudication promotion.

Discriminator status token:
- `EMP_EM_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`

Artifact bundle:
- `EMP_EM_01_ARTIFACT_v0: em_empirical_discriminator_emp_em_01_run_cycle01_v0`
- `EMP_EM_01_ARTIFACT_SHA256_v0: 90bd4e0c64a059c181c964cd954ddac5c57a3c5f6d7cc3d8fe7b8c9ee9931b42`
- `EMP_EM_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/em_empirical_discriminator_emp_em_01_run_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_em_empirical_discriminator_emp_em_01_scaffold_gate.py`

Run semantics:
- `EMP_EM_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
- `EMP_EM_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
- pass/fail outcome is bounded to the declared lane and candidate scope in the run artifact.

Execution lane pointers:
- derivation lane policy pointer:
  - `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- bridge evidence lane pointer:
  - `formal/docs/paper/RESULTS_TABLE_v0.md`

Scope statement:
- this target pins one bounded discriminator run for EM with explicit pass/fail prune semantics.
- it does not assert that EM is empirically validated.