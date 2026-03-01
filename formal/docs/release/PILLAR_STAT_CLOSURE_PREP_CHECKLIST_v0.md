# PILLAR-STAT Closure Prep Checklist v0

Spec ID:
- `PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the active-stage closure-prep lane for `PILLAR-STAT` after activation and before any earned `ACTIVE -> CLOSED` transition.
- Make the current open, blocked, non-promotional closeout posture machine-checkable.

Non-claim boundary:
- planning/control artifact only.
- does not authorize `ACTIVE -> CLOSED` by itself.
- does not discharge STAT adjudication tokens by itself.
- does not promote `TOE-STAT-DER-01` or `TOE-STAT-DER-02` by itself.
- does not broaden STAT scope beyond bounded theorem-surface execution.

Current authoritative posture:
- `PILLAR-STAT` remains `ACTIVE` in canonical roadmap/matrix surfaces.
- `PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION` remains `ACTIVE_PREEXECUTION_v0_NONDISCHARGED`.
- `PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION` remains `ACTIVE_PREEXECUTION_v0_NONDISCHARGED`.
- Required STAT closure rows remain active-stage blocked execution rows: `TOE-STAT-DER-01`, `TOE-STAT-DER-02` stay `B-BLOCKED`.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/RESULTS_TABLE_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md`
- `formal/docs/release/PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0.md`

Current closure-prep posture tokens:
- `PILLAR-STAT_PHYSICS_STATUS: OPEN_v0_ACTIVE_PREEXECUTION`
- `PILLAR-STAT_GOVERNANCE_STATUS: OPEN_v0_REQUIRED_ROWS_BLOCKED_EXECUTION`
- `PROCEED_GATE_STAT: BLOCKED_v0_PHYSICS_NOT_CLOSED`
- `MATRIX_CLOSURE_GATE_STAT: BLOCKED_v0_GOVERNANCE_NOT_CLOSED`
- `REQUIRED_STAT_CLOSURE_ROWS: TOE-STAT-DER-01,TOE-STAT-DER-02`

## Closure-Prep Checklist

### Gate A - dual-layer posture integrity (must be true now)
1. `PILLAR-STAT` remains `ACTIVE` in roadmap and matrix surfaces.
2. The roadmap and state surfaces mirror the same five closure-prep tokens exactly once.
3. `PROCEED_GATE_STAT` remains `BLOCKED_*` while `PILLAR-STAT_PHYSICS_STATUS` is `OPEN_*`.
4. `MATRIX_CLOSURE_GATE_STAT` remains `BLOCKED_*` while `PILLAR-STAT_GOVERNANCE_STATUS` is `OPEN_*`.

Pass evidence:
- `formal/python/tests/test_stat_dual_closure_posture_gate.py` passes.
- `formal/python/tests/test_pillar_dual_layer_gate_template.py` passes.

### Gate B - required row posture remains pre-closure (must be true now)
1. `REQUIRED_STAT_CLOSURE_ROWS` resolves to exactly `TOE-STAT-DER-01,TOE-STAT-DER-02`.
2. Each required row exists exactly once in `formal/docs/paper/RESULTS_TABLE_v0.md`.
3. Each required row remains `B-BLOCKED` while `PILLAR-STAT` is pre-discharge.
4. No required row is silently promoted during closure-prep-only changes.

Pass evidence:
- `formal/python/tests/test_stat_dual_closure_posture_gate.py` passes.
- `formal/python/tests/test_results_table_integrity.py` passes.

### Gate C - future closeout prerequisites are explicit (must stay blocked until earned)
1. `PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION` may change to `DISCHARGED_*` only when theorem/discharge surfaces actually earn it.
2. `PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION` may change to `DISCHARGED_*` only when inevitability closure is earned.
3. `TOE-STAT-DER-01` and `TOE-STAT-DER-02` must be non-placeholder and non-`B-*` before matrix closure is attempted.
4. `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json` must include `PILLAR-STAT` if the generic full-discharge mechanics lane is used for closure.
5. `formal/docs/release/PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0.md` defines the bounded file set and validation commands for the eventual closeout patch.

Pass evidence:
- `formal/python/tests/test_stat_closure_changeset_template_structure_gate.py` passes.

### Gate D - minimum closure-prep gate pack (must be green)
Required tests:
- `formal/python/tests/test_stat_dual_closure_posture_gate.py`
- `formal/python/tests/test_stat_closure_changeset_template_structure_gate.py`
- `formal/python/tests/test_pillar_dual_layer_gate_template.py`
- `formal/python/tests/test_pillar_status_matrix_consistency_gate.py`
- `formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
- `formal/python/tests/test_authority_token_single_definition_gate.py`
- `formal/python/tests/test_results_table_integrity.py`

Command:
```powershell
python -m pytest formal/python/tests/test_stat_dual_closure_posture_gate.py formal/python/tests/test_stat_closure_changeset_template_structure_gate.py formal/python/tests/test_pillar_dual_layer_gate_template.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_results_table_integrity.py
```

## Decision tokens
- `STAT_CLOSURE_PREP_DUAL_LAYER_POSTURE_v0: PASS | FAIL`
- `STAT_CLOSURE_PREP_REQUIRED_ROWS_v0: PASS | FAIL`
- `STAT_CLOSURE_PREP_FUTURE_CLOSEOUT_PATH_v0: PASS | FAIL`
- `STAT_CLOSURE_PREP_GATEPACK_v0: PASS | FAIL`
- `STAT_CLOSURE_PREP_FINAL_v0: ACTIVE_OPEN_TRACKED | CLOSURE_READY | NOT_READY`

Decision rule:
- Emit `ACTIVE_OPEN_TRACKED` only when Gates A, B, and D are `PASS` and Gate C remains explicitly blocked-but-defined.
- Emit `CLOSURE_READY` only when STAT adjudication tokens are discharged, required closure rows are non-placeholder/non-`B-*`, and the bounded closure changeset is ready to apply.
