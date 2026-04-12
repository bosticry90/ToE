# Physics Progress Ledger Policy (2026-04-11)

## Status
- ACTIVE
- Date: 2026-04-11
- Class: POLICY_NONCLAIM

## Objective
Define one canonical ledger payload for blocker-linked progress classification so governance-clean tranches are not misclassified as physics advancement without blocker-state movement evidence.

## Required ledger fields
- `schema_id`
- `captured_at_utc`
- `matrix_pointer`
- `tgc92_pointer`
- `tgc93_pointer`
- `blocker_counts`
- `target_blocker_state_change`
- `actual_blocker_state_change`
- `progress_classification`
- `evidence_pointer`

## Classification semantics
- `PROGRESS`: use only when blocker-state movement evidence is present and linked.
- `MAINTENANCE`: use when governance/control work is valid but blocker-state movement is absent.
- `REWORK_ROUTED`: use when branch policy routes tranche sequence to blocker-facing rework.

## Rule
- A physics-progress claim is not authorized unless ledger classification is `PROGRESS` and blocker-state movement is explicit in `actual_blocker_state_change`.

## Non-claim boundary
This policy governs repository-local execution classification and does not assert global physics adequacy claims.
