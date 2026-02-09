# BRIDGE_PROGRAM_T2_CAUSALITY_CLASSIFIER (design-only)

Opened: 2026-02-05

## Purpose

Classify each `v5_t2` flipped probe as:
- `single_root_phase_to_pair`
- `dual_root_phase_and_pair`
- `out_of_scope`

This classifier is deterministic and documentation-only in this ticket.

## Inputs (pinned)

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json` (baseline)
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`

Required per-probe fields:
- baseline signature
- `v5_t2` signature
- reason codes for:
  - `toyh_phase`
  - `toyh_phase_anchor`
  - `toyh_phase_bridge`
  - `toyh_current_bridge`
  - `toyg_bridge`
  - `toyhg_pair_bridge`

## Decision tree

1. If baseline signature is not `P-P-P` or `v5_t2` signature is `P-P-P`:
   - classify `out_of_scope`.
2. Else if:
   - `toyh_phase` is `FAIL_PHASE_INVARIANCE_TOL`,
   - `toyh_phase_anchor` is `FAIL_PHASE_INVARIANCE_TOL`,
   - `toyhg_pair_bridge` is `FAIL_PAIR_PHASE_MISMATCH`,
   - and both `toyh_current_bridge` and `toyg_bridge` are pass,
   - classify `single_root_phase_to_pair`.
3. Else if pair remains failed after phase lanes are pass-capable on the same profile:
   - classify `dual_root_phase_and_pair`.
4. Else:
   - classify `dual_root_phase_and_pair` (conservative default).

## Current v5_T2 classification result (pinned)

From `BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json` + `BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`:
- flipped probes from baseline: 13
- `single_root_phase_to_pair`: 13
- `dual_root_phase_and_pair`: 0
- `out_of_scope`: 0

## Interpretation guardrails

- This is a design-only causal hypothesis, not a proof.
- If future probes show pair failure with phase pass under `v5_t2`, reroute to dual-root lane planning immediately.

