# STATE_CORE_GENERATED_FIRST_CUTOVER_POLICY_v0

Status: ACTIVE
Effective date: 2026-03-26

## Scope
This policy governs the canonical control-plane families rendered from `formal/docs/release/state_core_v0.json` by `formal/python/tools/render_state_core_mirrors.py`.

Migrated control families in scope:
- Lane state and queued-lane state
- WS-10 branch/boundary authorization family
- WS task/status table family
- WS evidence-log/checkpoint-entry family
- WS scientific artifact lineage metadata family (bounded tranche)
- WS scientific artifact gate metadata family (bounded tranche)
- WS additive-candidate declaration metadata family (bounded tranche)

## Canonical Edit Path (Generated-First)
The default canonical edit path is:
1. Edit `formal/docs/release/state_core_v0.json`.
2. Run renderer apply/verify:
   - `./py.ps1 -m formal.python.tools.render_state_core_mirrors --apply-mirrors --verify-mirrors`
3. Run governance:
   - `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`

No other edit path is canonical for generated control-plane sections.

## Prohibition Rule
Direct human edits inside generated marker blocks are prohibited.

Prohibited block pattern:
- `<!-- GENERATED: ... -->`
- content lines inside the block
- `<!-- /GENERATED: ... -->`

If a generated block needs to change, update `state_core_v0.json` and rerender.

## Enforcement
- Integrity gate: `formal/python/tests/test_state_core_generation_integrity_gate.py`
- Manual-edit prohibition gate: `formal/python/tests/test_state_core_generated_block_manual_edit_prohibition_gate.py`

These gates are required in default governance execution.

## Operator Workflow
Operator workflow is fixed for migrated control families:
- Edit state core data only.
- Rerender mirrors.
- Run governance.

Manual mirror editing in generated sections is not an authorized workflow.

## Commit Discipline (Generated Snippets)
Generated snippet artifacts are excluded from commit by default:
- `formal/output/state_core_generated/state_core_tracker_snippet_v0.md`
- `formal/output/state_core_generated/state_core_ws10_snippet_v0.md`

These snippets are local renderer outputs and are not required as canonical committed artifacts.

## Next-Family Selection Rule
Before migrating another family, enforce all of the following:
- Migrate exactly one bounded family per tranche.
- Keep `manual_surface_compression_ratio >= 4.0`.
- Keep `governance_gate_default_enforced: true`.
- Require renderer apply/verify plus governance green before merge.
