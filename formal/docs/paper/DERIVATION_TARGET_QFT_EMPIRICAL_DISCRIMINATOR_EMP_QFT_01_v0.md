# Derivation Target: QFT Empirical Discriminator EMP-QFT-01 v0

Spec ID:
- `DERIVATION_TARGET_QFT_EMPIRICAL_DISCRIMINATOR_EMP_QFT_01_v0`

Target ID:
- `TARGET-QFT-EMPIRICAL-DISCRIMINATOR-EMP-QFT-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Define one bounded, non-claim discriminator package for the QFT lane.
- Establish a machine-checkable bridge from artifact to elimination-facing decision posture.

Non-claim boundary:
- bounded discriminator run package.
- no external truth claim.
- no automatic adjudication promotion.

Discriminator status token:
- `EMP_QFT_01_DISCRIMINATOR_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`

Artifact bundle:
- `EMP_QFT_01_ARTIFACT_v0: qft_empirical_discriminator_emp_qft_01_run_cycle01_v0`
- `EMP_QFT_01_ARTIFACT_SHA256_v0: 7b23eebf8deaac1ebe61fdcd2a0fd401e412e776eed4004fd8a9db89f15a4580`
- `EMP_QFT_01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/qft_empirical_discriminator_emp_qft_01_run_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_qft_empirical_discriminator_emp_qft_01_scaffold_gate.py`

Run semantics:
- `EMP_QFT_01_PRUNE_DECISION_v0: ELIMINATION_READY_BOUNDED_v0`
- `EMP_QFT_01_PRUNE_RESULT_v0: PASS_AND_PRUNE_SIGNAL_PRESENT_v0`
- pass/fail outcome is bounded to the declared lane and candidate scope in the run artifact.

Execution lane pointers:
- derivation lane policy pointer:
  - `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`
- bridge evidence lane pointer:
  - `formal/docs/paper/RESULTS_TABLE_v0.md`

Scope statement:
- this target pins one bounded discriminator run for QFT with explicit pass/fail prune semantics.
- it does not assert that QFT is empirically validated.