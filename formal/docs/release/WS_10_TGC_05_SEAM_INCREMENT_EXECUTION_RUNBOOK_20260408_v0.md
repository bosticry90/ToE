# WS-10 TGC-05 Seam Increment Execution Runbook (2026-04-08)

## Status
- ACTIVE
- Date: 2026-04-08
- Tranche: TGC-05
- Class: SEAM_INCREMENT_EXECUTION_RUNBOOK_NONCLAIM

## Objective
Execute one bounded seam increment for ROW-SEAM-QFT-GR-001 and record post-increment verification evidence.

## Preconditions
1. TGC-03 checkpoint is present and valid.
2. No unauthorized scope expansion is introduced.
3. Hold-policy constraints remain in force.

## Execution boundary
- Active row: ROW-SEAM-QFT-GR-001
- Allowed surfaces: existing active seam objective and already-pinned cycle11 seam chain surfaces.
- Prohibited: new authority surfaces without explicit reauthorization.

## Command bundle
1. Focused seam gate bundle:
   - ./py.ps1 -m pytest -q formal/python/tests/test_toe_qft_gr_seam_reactivation_objective_gate.py formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle10_to_11_synthesis_gate.py formal/python/tests/test_toe_seam_status_split_gate.py
2. Authority sanity bundle:
   - ./py.ps1 -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py

## Stop conditions
- Any focused seam gate failure.
- Any authority parity regression.
- Any scope drift outside bounded surfaces.

## Output requirements
- Decision checkpoint JSON with command results and decision state.
- Matrix row status update for ROW-SEAM-QFT-GR-001.

## Linkage
- Program: formal/docs/release/WS_10_GLOBAL_COMPLETION_EXECUTION_PROGRAM_20260408_v0.md
- Matrix: formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md
- Prior checkpoint: formal/output/ws10_tgc03_seam_increment_authorization_checkpoint_20260408_v0.json
