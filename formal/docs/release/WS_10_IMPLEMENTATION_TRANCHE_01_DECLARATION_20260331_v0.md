# WS-10 Implementation Tranche 01 Declaration (2026-03-31)

Tranche one-sentence declaration:
- Objective: add one narrow governance gate improvement that enforces the checkpoint ladder contract as executable policy.
- Allowed files:
  - formal/python/tests/test_checkpoint_ladder_contract_gate.py (new)
  - checkpoint_ladder.ps1 (only if minimally required by failing contract assertions)
- Success condition: checkpoint ladder all green and clean tree post-restore.
- Rollback point: 8b9aabe.

## Tranche Header

- Tranche name: WS-10 Implementation Tranche 01 - Checkpoint Ladder Contract Gate
- Objective: enforce that checkpoint_ladder.ps1 remains the required four-step bounded-tranche verification runner.
- Allowed files:
  - formal/python/tests/test_checkpoint_ladder_contract_gate.py
  - checkpoint_ladder.ps1 (conditional, minimal edits only)
- Out of scope:
  - all state-core JSON artifacts
  - all authority/parity surfaces
  - all unrelated tests/tools/docs
  - any multi-file protocol redesign
- Acceptance: checkpoint_ladder.ps1 all green.
- Rollback anchor: 8b9aabe

## Contract Assertions To Implement

1. The ladder script contains all required steps in order:
   - renderer apply/verify
   - state-core integrity gate
   - compression/yield gate
   - governance suite
2. The ladder script restores generated state-core outputs at the end.
3. The ladder script exits non-zero on any failed step.

## Execution Rule

1. Do not edit any file outside the allowed-files list.
2. If a third file changes, stop and rollback to 8b9aabe.
3. After implementation, run checkpoint_ladder.ps1.
4. Accept tranche only if all four steps pass and the tree is clean afterward.