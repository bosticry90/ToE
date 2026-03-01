# Pillar Closure Standard v0

Spec ID:
- `PILLAR_CLOSURE_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Standardize how pillar closeout posture is declared and enforced across current and future pillars.
- Require a dual-layer closure token set for every pillar admitted to the canonical pillar matrix.
- Require generic discharge-registry enrollment for every pillar that is already `CLOSED`.

Non-claim boundary:
- policy/control artifact only.
- does not close a pillar by itself.
- does not discharge adjudication tokens by itself.
- does not promote results-table rows by itself.
- does not broaden theorem scope or external-truth claims.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json`
- `formal/python/tests/test_pillar_dual_layer_gate_template.py`
- `formal/python/tests/test_pillar_full_discharge_completion_mechanics.py`
- `formal/python/tests/test_pillar_closure_standard_coverage_gate.py`

## Standard rules

### 1) Matrix-admission rule
Any pillar admitted to `PILLAR_STATUS_MATRIX_v1.json` must define exactly one roadmap token each for:
- `PILLAR-*_PHYSICS_STATUS`
- `PILLAR-*_GOVERNANCE_STATUS`
- `PROCEED_GATE_*`
- `MATRIX_CLOSURE_GATE_*`
- `REQUIRED_*_CLOSURE_ROWS`

### 2) Active-pillar rule
Any `ACTIVE` pillar must carry an explicit closure-prep posture.
- `PILLAR-*_PHYSICS_STATUS` must remain `OPEN_*` until the physics/discharge layer is actually closed.
- `PILLAR-*_GOVERNANCE_STATUS` must remain `OPEN_*` until required closure rows and governance prerequisites are actually closed.
- `PROCEED_GATE_*` and `MATRIX_CLOSURE_GATE_*` must remain `BLOCKED_*` while the pillar is non-discharged.

### 3) Closed-pillar rule
Any pillar with `matrix_status = CLOSED` in `PILLAR_STATUS_MATRIX_v1.json` must have exactly one registry entry in `PILLAR_DISCHARGE_REGISTRY_v0.json`.
- The registry entry must point to the canonical discharge doc.
- The roadmap `REQUIRED_*_CLOSURE_ROWS` token must match the registry `required_results_rows` list exactly.
- Generic completion mechanics are then enforced by `formal/python/tests/test_pillar_full_discharge_completion_mechanics.py`.

### 4) Future-pillar rule
Any future pillar promoted into `PILLAR_STATUS_MATRIX_v1.json` must satisfy Rule 1 in the same change set as matrix admission.
- If admitted as `ACTIVE`, it must satisfy Rule 2.
- It may not transition to `CLOSED` until it satisfies Rule 3.

### 5) Locked-queue rule
A locked queue pillar may defer closure tokens until activation or matrix admission.
- Once it is admitted to the matrix, this standard becomes mandatory.
