# Derivation Target: SR Empirical Discriminator EMP-SR-01 v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_DISCRIMINATOR_EMP_SR_01_v0`

Target ID:
- `TARGET-SR-EMPIRICAL-DISCRIMINATOR-EMP-SR-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one bounded, non-claim discriminator package for the SR lane.
- Establish a machine-checkable bridge from artifact to elimination-facing decision posture.

Non-claim boundary:
- bounded discriminator run package.
- no external truth claim.
- no automatic adjudication promotion.

Discriminator status token:
- `EMP_SR_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`

Artifact bundle:
- `EMP_SR_01_ARTIFACT_v0: sr_empirical_discriminator_emp_sr_01_run_cycle01_v0`
- `EMP_SR_01_ARTIFACT_SHA256_v0: 2f2e200035413a0ae3f7be863c5b46f01cfe62ac4fd511b4711cb57d433ff023`
- `EMP_SR_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/sr_empirical_discriminator_emp_sr_01_run_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_sr_empirical_discriminator_emp_sr_01_scaffold_gate.py`

Run semantics:
- `EMP_SR_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
- `EMP_SR_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
- pass/fail outcome is bounded to the declared lane and candidate scope in the run artifact.

Execution lane pointers:
- derivation lane policy pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- bridge evidence lane pointer:
  - `formal/docs/paper/RESULTS_TABLE_v0.md`

Scope statement:
- this target pins one bounded discriminator run for SR with explicit pass/fail prune semantics.
- it does not assert that SR is empirically validated.
