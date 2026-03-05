# COSMO Micro21 Opening Checklist v0

Spec ID:
- `COSMO_MICRO21_OPENING_CHECKLIST_v0`

Purpose:
- Open a new canonical tranche at `micro21` without violating locked-queue cross-surface sync.
- Enforce ordering: canonical surfaces first, theorem-surface promotion second.

Precondition checkpoint:
- Commit: `5a7ae83` (`cosmo: checkpoint micro14-micro20 strict-sync tranche`)
- Verified broad selector baseline:
  - `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest formal/python/tests -k "cosmo_bg_micro or cosmo_full_derivation" -q`

## Step 1: Add Canonical Micro21 Surface Entries

Required updates:
- Add `micro21` target lock lines in:
  - `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- Add `micro21` policy/doc/gate fields in:
  - `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- Add corresponding cross-pin expectations in:
  - `formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py`

Required artifacts to introduce:
- `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_21_*.md`
- `formal/output/cosmo_bg_micro21_*_cycle01_v0.json`
- `formal/python/tests/test_cosmo_bg_micro21_*_gate.py`

Gate for this step:
- `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest formal/python/tests/test_cosmo_bg_micro21*_gate.py formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py -q`

## Step 2: Promote Theorem-Surface Sync For Micro21

Required updates:
- Append `micro21` theorem token in:
  - `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json` (COSMO `required_theorem_surfaces`)
- Add matching Lean scaffold token in:
  - `formal/toe_formal/ToeFormal/Cosmology/BackgroundObjectScaffold.lean`

Gate for this step:
- `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest formal/python/tests/test_cosmo_bg_micro20*_gate.py formal/python/tests/test_cosmo_bg_micro21*_gate.py formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py -q`

## Step 3: Pillar-Level Governance Verification

Required gate pack:
- `formal/python/tests/test_cosmo_background_kickoff_gate.py`
- `formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py`
- `formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py`
- `formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py`
- `formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py`

Command:
- `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest formal/python/tests/test_cosmo_background_kickoff_gate.py formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py -q`

## Step 4: Broad COSMO Regression

Command:
- `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest formal/python/tests -k "cosmo_bg_micro or cosmo_full_derivation" -q`

Pass criteria:
- No new failures.
- No matrix/state cross-pin drift.
- COSMO lane remains `LOCKED` until explicit unlock policy conditions are satisfied.

## Step 5: Commit Discipline

Commit boundary rules:
- Commit A: canonical micro21 opening surfaces (target + matrix + crosspin + micro21 doc/test/artifact).
- Commit B: theorem-surface sync promotion (registry + Lean).
- Commit C (optional): any follow-up policy hardening if required by gate deltas.
