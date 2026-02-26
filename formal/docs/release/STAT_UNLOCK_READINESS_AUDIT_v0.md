# STAT Unlock Readiness Audit v0

Spec ID:
- `STAT_UNLOCK_READINESS_AUDIT_v0`

Classification:
- `P-POLICY`

Purpose:
- Execute a pre-activation readiness audit lane for `PILLAR-STAT` under locked status.
- Enumerate prerequisite closure checks, blocker-row checks, and anti-drift conditions before any unlock attempt.

Non-claim boundary:
- diagnostics-only artifact.
- non-claim control surface.
- no adjudication-token flips.
- no pillar-matrix status change authorization.
- no roadmap activation authorization by itself.

Current authoritative posture:
- `PILLAR-STAT` remains `LOCKED` in roadmap pillar table.
- canonical five-pillar set (`QFT`, `QM`, `GR`, `EM`, `SR`) remains bounded discharged and matrix-closed under current scope.
- downstream queue discipline remains frozen (`QFT -> STAT -> COSMO`) under roadmap sequencing rules.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/RESULTS_TABLE_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md`
- activation changeset template pointer: `formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md`
- matrix-prep checklist pointer: `formal/docs/release/STAT_MATRIX_PREP_CHECKLIST_v0.md`

## Readiness audit checklist (pre-activation only)

### A. Structural prerequisites
1. `PILLAR-STAT` row exists in roadmap table with `Status = LOCKED`.
2. `PILLAR-STAT` target remains `TARGET-TH-ENTROPY-PLAN`.
3. Prerequisite for `PILLAR-STAT` remains `TARGET-GR01-DERIV-CHECKLIST-PLAN`.
4. Claim-prefix map remains pinned: `TOE-STAT-* -> TARGET-TH-ENTROPY-PLAN`.
5. Exact STAT authority token names and placeholder values are pre-pinned in `DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md` and the activation changeset template, but are not mirrored cross-surface while `PILLAR-STAT` is `LOCKED`.

### B. Prerequisite closure integrity
1. `PILLAR-GR` remains `CLOSED` in canonical matrix surfaces.
2. Required GR closure rows declared by roadmap token `REQUIRED_GR_CLOSURE_ROWS` are present in `RESULTS_TABLE_v0.md`.
3. Each required GR closure row is non-`B-*`.
4. Reserved STAT closure rows (`TOE-STAT-DER-01`, `TOE-STAT-DER-02`) are present in `RESULTS_TABLE_v0.md` and remain locked-stage placeholders (non-activating).

### C. Non-circularity / dependency hygiene
1. `PILLAR-QFT` roadmap prerequisites do not include `TARGET-TH-ENTROPY-PLAN`.
2. STAT entropy-target docs do not import `ASM-QM-*` or `ASM-QFT-*` assumption IDs at this locked readiness stage.
3. No closed-pillar dependency path routes back into `PILLAR-STAT`.

### D. Gate posture before any activation proposal
1. `formal/python/tests/test_stat_unlock_prerequisite_integrity_gate.py` passes.
2. `formal/python/tests/test_stat_no_circular_dependency_with_closed_pillars.py` passes.
3. `formal/python/tests/test_stat_readiness_placeholder_structure_gate.py` passes.
4. `formal/python/tests/test_stat_authority_token_preset_lock_gate.py` passes.
5. `formal/python/tests/test_stat_activation_changeset_template_structure_gate.py` passes.
6. `formal/python/tests/test_results_table_integrity.py` passes.
7. `formal/python/tests/test_stat_unlock_readiness_pack_gate.py` passes (executes the pinned readiness gate pack while `PILLAR-STAT` is `LOCKED`).
8. Global drift guards remain green:
   - `formal/python/tests/test_pillar_status_matrix_consistency_gate.py`
   - `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
   - `formal/python/tests/test_authority_token_single_definition_gate.py`

## Readiness verdict tokens (diagnostic only)
- `STAT_UNLOCK_READINESS_PREREQUISITES_v0: PASS | FAIL`
- `STAT_UNLOCK_READINESS_REQUIRED_ROWS_v0: PASS | FAIL`
- `STAT_UNLOCK_READINESS_NONCIRCULARITY_v0: PASS | FAIL`
- `STAT_UNLOCK_READINESS_DRIFT_GUARDS_v0: PASS | FAIL`
- `STAT_UNLOCK_READINESS_FINAL_VERDICT_v0: READY_LOCKED_ONLY | NOT_READY`

Decision rule:
- Emit `READY_LOCKED_ONLY` only when all four checks are `PASS`.
- Even under `READY_LOCKED_ONLY`, no `LOCKED -> ACTIVE` transition is authorized by this audit artifact.
