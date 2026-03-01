# PILLAR-STAT Closure Changeset Template v0

Spec ID:
- `PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0`

Classification:
- `P-POLICY`

Purpose:
- Constrain the eventual `PILLAR-STAT` `ACTIVE -> CLOSED` patch to an explicit, reviewable, bounded fileset.
- Prevent a matrix closure flip before discharged adjudications and row promotions are actually earned.

Non-claim boundary:
- planning/execution-template artifact only.
- not a closure by itself.
- does not discharge STAT adjudication tokens by itself.
- does not authorize row promotion without earned evidence.
- does not broaden STAT scope beyond bounded theorem/discharge surfaces.

Canonical anchors:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `formal/docs/paper/RESULTS_TABLE_v0.md`
- `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json`
- `State_of_the_Theory.md`
- `formal/docs/release/PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md`

## Preconditions (must be true before preparing closure patch)

1. `PILLAR-STAT` remains `ACTIVE` before the closeout patch is applied.
2. `PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION` is `DISCHARGED_*`.
3. `PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION` is `DISCHARGED_*`.
4. `TOE-STAT-DER-01` and `TOE-STAT-DER-02` are no longer `P-POLICY` placeholders and are non-`B-*`.
5. `PILLAR-STAT_PHYSICS_STATUS` and `PILLAR-STAT_GOVERNANCE_STATUS` are ready to move from `OPEN_*` to `CLOSED_*`.
6. `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json` already includes `PILLAR-STAT` or is updated in the same bounded change set.

## Mandatory Files To Touch (single atomic closeout change set)

1. `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
   - Change the canonical `PILLAR-STAT` row status from `ACTIVE` to `CLOSED`.
   - Update `PILLAR-STAT_PHYSICS_STATUS` and `PILLAR-STAT_GOVERNANCE_STATUS` to `CLOSED_*`.
   - Update `PROCEED_GATE_STAT` and `MATRIX_CLOSURE_GATE_STAT` to `ALLOWED_*`.
   - Preserve `REQUIRED_STAT_CLOSURE_ROWS` as the exact closure-row list.

2. `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
   - Change `PILLAR-STAT` `matrix_status` from `ACTIVE` to `CLOSED`.
   - Synchronize `full_derivation` and `inevitability` to discharged values.

3. `formal/docs/paper/RESULTS_TABLE_v0.md`
   - Promote `TOE-STAT-DER-01` and `TOE-STAT-DER-02` out of placeholder posture.
   - Ensure both required closure rows are non-`B-*` after promotion.

4. `formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json`
   - Add or update the `PILLAR-STAT` registry entry used by `formal/python/tests/test_pillar_full_discharge_completion_mechanics.py`.

5. `State_of_the_Theory.md`
   - Mirror the final STAT closure tokens exactly once.
   - Record a bounded closeout checkpoint note without external-truth broadening.

## Forbidden Edits In This Closure Patch

- Do not close `PILLAR-STAT` while `TOE-STAT-DER-01` or `TOE-STAT-DER-02` remains `P-POLICY`.
- Do not close `PILLAR-STAT` while any required STAT closure row remains `B-*`.
- Do not alter non-STAT pillar statuses in the STAT closure patch.
- Do not broaden STAT scope into cosmology, QFT-statistical, black-hole, or holographic claims.
- Do not skip registry wiring if generic full-discharge mechanics are being relied upon.

## Required STAT Closure Tokens

Pinned token names:
- `PILLAR-STAT_PHYSICS_STATUS`
- `PILLAR-STAT_GOVERNANCE_STATUS`
- `PROCEED_GATE_STAT`
- `MATRIX_CLOSURE_GATE_STAT`
- `REQUIRED_STAT_CLOSURE_ROWS`

Transition requirement:
- Current closure-prep posture is `OPEN/BLOCKED`.
- Closure patch must transition these tokens to `CLOSED/ALLOWED` only when preconditions are fully satisfied.

## Exact Validation Commands

### A. Pre-closeout readiness (ACTIVE posture; run before editing)

```powershell
python -m pytest formal/python/tests/test_stat_dual_closure_posture_gate.py formal/python/tests/test_stat_closure_changeset_template_structure_gate.py formal/python/tests/test_pillar_dual_layer_gate_template.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_results_table_integrity.py
```

### B. Post-closeout validation (CLOSED posture; run after editing)

```powershell
python -m pytest formal/python/tests/test_pillar_dual_layer_gate_template.py formal/python/tests/test_pillar_status_matrix_consistency_gate.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py formal/python/tests/test_authority_token_single_definition_gate.py formal/python/tests/test_results_table_integrity.py formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py formal/python/tests/test_pillar_full_discharge_completion_mechanics.py
```

## Closure Review Checklist

- `PILLAR-STAT` changed from `ACTIVE` to `CLOSED` in roadmap and matrix only after discharged adjudications were pinned.
- `TOE-STAT-DER-01` and `TOE-STAT-DER-02` were promoted out of placeholder posture.
- `PILLAR_DISCHARGE_REGISTRY_v0.json` includes a complete `PILLAR-STAT` entry if generic discharge mechanics are used.
- State/roadmap/matrix closure tokens are synchronized exactly once.
- No non-STAT pillar status or adjudication token changed.

## Closure Attestation Template

- `PILLAR-STAT_CLOSURE_CHANGESET_PRECHECK_v0: PASS | FAIL`
- `PILLAR-STAT_CLOSURE_CHANGESET_WIRING_v0: PASS | FAIL`
- `PILLAR-STAT_CLOSURE_CHANGESET_POSTGATES_v0: PASS | FAIL`
- `PILLAR-STAT_CLOSURE_CHANGESET_SCOPE_BOUNDARY_v0: PASS | FAIL`
- `PILLAR-STAT_CLOSURE_CHANGESET_NOTES_v0: <bounded rationale>`
