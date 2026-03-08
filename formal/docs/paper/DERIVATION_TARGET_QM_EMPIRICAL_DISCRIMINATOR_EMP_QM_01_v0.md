# Derivation Target: QM Empirical Discriminator EMP-QM-01 v0

Spec ID:
- `DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0`

Target ID:
- `TARGET-QM-EMPIRICAL-DISCRIMINATOR-EMP-QM-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one bounded, non-claim discriminator package for QM lane execution.
- Establish a machine-checkable bridge from artifact to elimination-facing decision posture.

Non-claim boundary:
- bounded discriminator run package.
- no external truth claim.
- no automatic adjudication promotion.

Discriminator status token:
- `EMP_QM_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`

Artifact bundle:
- `EMP_QM_01_ARTIFACT_v0: qm_empirical_discriminator_emp_qm_01_run_cycle02_v0`
- `EMP_QM_01_ARTIFACT_SHA256_v0: 5fad6fdfaa020303fd912dd5d1f31c112457d0978dffaefd7fd3c9c001da17f5`
- `EMP_QM_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/qm_empirical_discriminator_emp_qm_01_run_cycle02_v0.json`
- coupling gate path: `formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py`

Run semantics:
- `EMP_QM_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
- `EMP_QM_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
- pass/fail outcome is bounded to the declared lane and candidate scope in the run artifact.

Execution lane pointers:
- elimination lane policy pointer:
  - `formal/docs/lanes/OV-DR-BR-01_dr01_to_br01_eliminative_lane.md`
- existing bridge evidence lane pointer:
  - `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md`

Scope statement:
- this target pins one bounded discriminator run for QM with explicit pass/fail prune semantics.
- it does not assert that QM is empirically validated.
