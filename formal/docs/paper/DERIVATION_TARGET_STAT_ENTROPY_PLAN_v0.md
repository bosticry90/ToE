# Derivation Target: STAT Entropy Plan v0

Spec ID:
- `DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0`

Target ID:
- `TARGET-TH-ENTROPY-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Provide a locked-status skeleton target for STAT entropy-lane full-derivation planning.
- Define required structure and discharge-row placeholders without activating `PILLAR-STAT`.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no full statistical mechanics completion claim.
- no external truth claim.

Activation posture:
- `PILLAR-STAT` remains `LOCKED` until explicit unlock prerequisites and governance gates are satisfied.
- this document does not authorize `LOCKED -> ACTIVE` transitions.

Authority token preset (pre-activation, non-authoritative naming freeze):
- `PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION: ACTIVE_PREEXECUTION_v0_NONDISCHARGED`
- `PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: ACTIVE_PREEXECUTION_v0_NONDISCHARGED`
- `STAT_AUTHORITY_TOKEN_PRESET_LOCK_v0: PINNED_NAMES_AND_PLACEHOLDER_VALUES_LOCKED_STAGE_ONLY`
- These tokens are pre-pinned here to eliminate naming decisions before activation.
- While `PILLAR-STAT` is `LOCKED`, do not mirror these token definitions into `PHYSICS_ROADMAP_v0.md`, `State_of_the_Theory.md`, or `PILLAR_STATUS_MATRIX_v1.json`.

Minimum structural objects required:
- entropy / entropy-production object surface.
- flux / balance law object surface.
- regime assumptions object surface (equilibrium or bounded non-equilibrium).
- admissibility / causality / positivity constraints object surface.

Required discharge rows (reserved placeholders; non-authoritative until wired):
- `TOE-STAT-DER-01` (entropy-balance theorem surface placeholder)
- `TOE-STAT-DER-02` (regime-validity and closure-coupling placeholder)

Evidence adequacy placeholder:
- `EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0: NOT_PRESENT_v0`
- `EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0: MIN_5_ENTRIES_REQUIRED`

Cycle01 evidence-checkpoint artifact scaffold (active pre-discharge structural checkpoint):
- `STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0: stat_evidence_checkpoint_cycle01_v0`
- `STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0: 7322727f0e7ff87e127127a08228ea5e6bf46250b15698cfb9dfe6a6b766ca25`
- `STAT_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `STAT_EVIDENCE_CHECKPOINT_CYCLE01_COUPLING_GATE_BINDING_v0: BOUND_TO_TEST_PATH_v0`
- artifact path: `formal/output/stat_evidence_checkpoint_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py`
- non-claim boundary remains explicit and binding for this artifact.
- bounded scaffold scope only; no entropy derivation discharge claim, no adequacy completion claim, and no external truth claim.
- required content fields (placeholder schema list):
  - `artifact_id`
  - `cycle_id`
  - `target_id`
  - `scope_boundary`
  - `assumption_freeze_refs`
  - `required_results_rows_refs`
  - `cross_surface_pointers`
  - `artifact_sha256`
- hash pin requirement:
  - artifact SHA256 token is now pinned to the produced Cycle01 structural checkpoint payload hash.
  - any future artifact revision must update the pinned SHA256 token and cross-surface pointers in the same change set.

Closure definition (locked-stage scaffold):
- typed thermo/stat theorem/derivation surface exists with explicit assumptions.
- explicit regime validity, bounded scope, and non-claims remain pinned.
- paper/state/results pointers are synchronized before any unlock proposal.

Explicit exclusions at this stage:
- no adjudication flip.
- no matrix-status change.
- no roadmap activation edit.
