# Derivation Target: STAT M2 Assumption Minimization Depth Exemplar Cycle02 v0

Spec ID:
- `DERIVATION_TARGET_STAT_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_v0`

Target ID:
- `TARGET-STAT-M2-ASSUMPTION-MINIMIZATION-DEPTH-EXEMPLAR-CYCLE02-v0`

Classification:
- `P-POLICY`

Purpose:
- Add one depth-completion exemplar lane for STAT M2 assumption minimization.
- Extend beyond cycle01 scaffold while preserving bounded non-claim posture.

Non-claim boundary:
- depth-exemplar/control surface only.
- no M2 status promotion by itself.
- no theorem promotion by itself.

Depth exemplar bundle:
- `STAT_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `STAT_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_ARTIFACT_v0: stat_m2_assumption_minimization_depth_exemplar_cycle02_v0`
- `STAT_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/stat_m2_assumption_minimization_depth_exemplar_cycle02_v0.json`
- gate path: `formal/python/tests/test_stat_m2_assumption_minimization_depth_exemplar_cycle02_gate.py`