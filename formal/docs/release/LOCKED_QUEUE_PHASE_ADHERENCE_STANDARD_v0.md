# Locked-Queue Phase Adherence Standard v0

Spec ID:
- `LOCKED_QUEUE_PHASE_ADHERENCE_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Standardize machine-auditable phase-adherence snapshots for all `LOCKED_QUEUE` pillars.
- Keep locked-queue progression constrained to cross-surface parity without status flips.
- Ensure each locked pillar advertises one canonical wait-only posture across state/matrix/roadmap/registry.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not assert theorem discharge.
- does not authorize status promotion by itself.
- no external truth claim.

Canonical artifacts:
- standard pointer: `formal/docs/release/LOCKED_QUEUE_PHASE_ADHERENCE_STANDARD_v0.md`
- registry pointer: `formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json`
- matrix pointer: `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- roadmap pointer: `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- state pointer: `State_of_the_Theory.md`
- enforcement gate: `formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py`

Required snapshot token pattern (per locked pillar):
- `<PREFIX>_PHASE_ADHERENCE_SNAPSHOT_v0: LOCKED_QUEUE_CROSS_SURFACE_SYNCED`
- `<PREFIX>_PHASE_ADHERENCE_MATRIX_STATUS_v0: LOCKED`
- `<PREFIX>_PHASE_ADHERENCE_ROADMAP_STATUS_v0: LOCKED`
- `<PREFIX>_PHASE_ADHERENCE_REGISTRY_MODE_v0: LOCKED_QUEUE`
- `<PREFIX>_PHASE_ADHERENCE_PRIMARY_LANE_v0: <TARGET_ID>`
- `<PREFIX>_PHASE_ADHERENCE_GOVERNANCE_SUITE_v0: INCLUDED`

Prefix derivation rule:
- `PREFIX` is the pillar suffix from `PILLAR-<PREFIX>` with hyphens converted to underscores.
- Example: `PILLAR-COSMO -> COSMO`.

Cross-surface parity rule:
- For each `mode = LOCKED_QUEUE` row in the phase-advancement registry:
  - matrix row status must be `LOCKED`.
  - roadmap row status must be `LOCKED`.
  - registry row mode must be `LOCKED_QUEUE`.
  - state snapshot primary lane must equal the registry `target_id`.

Governance execution rule:
- `formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py`
  must be listed in `governance_suite.ps1`.