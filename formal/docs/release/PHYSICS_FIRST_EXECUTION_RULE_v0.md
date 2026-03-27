# PHYSICS_FIRST_EXECUTION_RULE_v0

## Status
- ACTIVE
- Date: 2026-03-26
- Classification: P-POLICY

## Objective
Enforce that active lane progression is driven by scientific progress rather than control-surface growth.

## Core Rule
An active tranche must declare one scientific delta class:
- `math_strengthening`
- `physics_compatibility`
- `blocker_discharge`
- `assumption_narrowing`
- `prediction_or_exclusion`

If none of these are present, the tranche is support work and cannot be promoted as the active scientific tranche.

## Support Work Classification
Allowed support-only categories:
- `mirror_generation`
- `parity_maintenance`
- `governance_hygiene`
- `tooling_refactor`

Support-only work can proceed only if it directly unblocks the current active scientific tranche or protects non-claim boundary integrity.

## Promotion Gate
A tranche promotion must fail when any of these are true:
1. missing scientific delta class,
2. scientific delta class outside the allowed list,
3. support-only tranche is marked active,
4. non-claim boundary is absent,
5. required gate evidence is missing.

## Concurrency Rule
- one active scientific lane at a time,
- at most one queued lane,
- all others paused.

## Invariants (Unchanged)
- release-gate truth: governance prerequisite plus full pytest branch-health.
- scalar freeze status remains unchanged.
- packet hold invariance remains unchanged.
- non-claim boundary wording remains unchanged.

## Verification Entry Point
- Gate: `formal/python/tests/test_physics_first_execution_rule_v0_gate.py`
- State core gate: `formal/python/tests/test_state_core_schema_v0_gate.py`
