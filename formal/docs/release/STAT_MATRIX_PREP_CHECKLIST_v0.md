# STAT Matrix Prep Checklist v0

Spec ID:
- `STAT_MATRIX_PREP_CHECKLIST_v0`

Classification:
- `P-POLICY`

Purpose:
- Define pre-activation matrix-preparation checks for `PILLAR-STAT`.
- Keep unlock engineering explicit while preserving `LOCKED` status.

Non-claim boundary:
- diagnostics/planning-only artifact.
- non-authoritative for matrix status by itself.
- no adjudication-token flips.
- no `LOCKED -> ACTIVE` authorization.

Scope discipline:
- This checklist is preparatory only.
- Canonical matrix authority remains `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`.
- Activation can only be proposed after readiness and governance gates are green.
- Activation patch choreography and exact validation commands are pinned in `formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md`.

## Pre-activation matrix prep checks

### 1) Row identity and target binding (must remain stable)
- Pillar ID: `PILLAR-STAT`
- Status (current): `LOCKED`
- Target binding: `TARGET-TH-ENTROPY-PLAN`
- Target artifact pointer: `formal/docs/paper/DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md`

### 2) Prerequisite closure mapping (must be explicit)
- Prerequisite token set for STAT row must include: `TARGET-GR01-DERIV-CHECKLIST-PLAN`.
- Prerequisite closure semantics must remain sourced from roadmap and matrix consistency gates.
- No prerequisite broadening is allowed in prep stage.

### 3) Cross-surface parity requirements (pre-activation)
- Roadmap table row for `PILLAR-STAT` remains `LOCKED` and token-aligned.
- State/readiness docs may annotate readiness only; they do not alter matrix authority.
- No duplicate or contradictory authority tokens are introduced.
- STAT authority token names/placeholder values may be pre-pinned in the STAT target doc + activation template, but must not be mirrored into roadmap/state/matrix while `PILLAR-STAT` remains `LOCKED`.

### 4) Blocker/readiness gating before any unlock proposal
- `formal/python/tests/test_stat_unlock_prerequisite_integrity_gate.py` passes.
- `formal/python/tests/test_stat_no_circular_dependency_with_closed_pillars.py` passes.
- `formal/python/tests/test_stat_readiness_placeholder_structure_gate.py` passes.
- `formal/python/tests/test_stat_authority_token_preset_lock_gate.py` passes.
- `formal/python/tests/test_stat_activation_changeset_template_structure_gate.py` passes.
- `formal/python/tests/test_results_table_integrity.py` passes.
- `formal/python/tests/test_stat_unlock_readiness_pack_gate.py` passes (aggregates the pinned pre-activation readiness gate pack).
- `formal/python/tests/test_pillar_status_matrix_consistency_gate.py` passes.
- `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py` passes.
- `formal/python/tests/test_authority_token_single_definition_gate.py` passes.

### 5) Activation-proposal package prerequisites (future, not executed here)
- A dedicated STAT discharge target doc exists and is synchronized.
- Required STAT closure rows are defined in the results surface.
- STAT Cycle01 evidence-checkpoint placeholder structure is defined (artifact ID, hash placeholder, and reserved coupling-gate path).
- Exact STAT authority token names and placeholder values are pre-pinned in `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md` and locked by test.
- STAT activation changeset template exists and pins exact preflight vs post-activation validation commands.
- Readiness verdict is `READY_LOCKED_ONLY` and drift guards are green.
- A separate, explicit governance change set is prepared for any proposed status transition.

## Decision tokens (prep-only)
- `STAT_MATRIX_PREP_ROW_BINDING_v0: PASS | FAIL`
- `STAT_MATRIX_PREP_PREREQ_BINDING_v0: PASS | FAIL`
- `STAT_MATRIX_PREP_PARITY_GUARDS_v0: PASS | FAIL`
- `STAT_MATRIX_PREP_GATEPACK_v0: PASS | FAIL`
- `STAT_MATRIX_PREP_FINAL_v0: PREP_COMPLETE_LOCKED | PREP_INCOMPLETE`

Decision rule:
- Emit `PREP_COMPLETE_LOCKED` only when all four checks are `PASS`.
- `PREP_COMPLETE_LOCKED` is not activation and does not change matrix status.
