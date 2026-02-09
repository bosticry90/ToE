# Supplementary: Reproducibility commands

This file is supplementary material for the CiSE submission. It contains repository-specific commands that are intentionally omitted from the main narrative.

Goal

- Deterministically reproduce the blocked outcome for an unauthorized comparison and verify the invariant.

Commands (repo-root)

1) Update the enforcement manifest:

- `./py.ps1 formal/python/tests/tools/update_admissibility_manifest.py`

2) Regenerate canonical locks for existing lanes:

- `./py.ps1 -m formal.python.tools.regen_canonical_locks --snd-only`
- `./py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only`

3) Verify the invariant:

- `./py.ps1 -m pytest -q formal/python/tests/test_ov_br_snd03_cross_lane_bridge_audit_lock.py`
