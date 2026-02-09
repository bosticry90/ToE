# BRIDGE_TICKET_TOYH_0005 — C6 phase stabilized bridge for v5_T2 closure

Status: Implementation (scoped; Lane L1 only)

Opened: 2026-02-05

## Purpose (bounded)

Restore bridge-program frontier closure under tolerance profile `v5_t2` by introducing a numerically stabilized Toy-H phase observable / comparator that preserves the conceptual phase invariant while improving conditioning at `toyh_tolerance = 1e-15`, without loosening any `v5_t2` tolerances.

This ticket targets the `mismatch_phase_and_pair` frontier and is explicitly single-root: fix phase tolerance brittleness -> pair mismatch should resolve downstream.

## Triggering evidence (pinned)

Design package (must remain unchanged while implementing):
- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_T2_0001_phase_and_pair_tight_tol_design.md`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_CAUSALITY_CLASSIFIER.md`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_LANE_PLAN.md`

Pinned v5_T2 mismatch artifacts:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT_v5_T2.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY_v5_T2.json`

Pinned mismatch summary:
- reason frontier: `mismatch_phase_and_pair`
- `n_mismatch = 13`
- all flipped probes are `both_fail` with:
  - `toyh_phase = FAIL_PHASE_INVARIANCE_TOL`
  - `toyh_phase_anchor = FAIL_PHASE_INVARIANCE_TOL`
  - `toyhg_pair_bridge = FAIL_PAIR_PHASE_MISMATCH`
  - `toyh_current_bridge` and `toyg_bridge` remain pass-capable

## Scope (what is allowed)

Allowed:
- Add a new stabilized phase-evaluation path and/or comparator used by:
  - `toyh_phase` and `toyh_phase_anchor` evaluation, and/or
  - the phase component consumed by `toyhg_pair_bridge`
- Add new deterministic helper(s) in the Toy-H C6 phase bridge module(s).
- Add tests and wire evidence pointers.

Not allowed:
- Any tolerance profile changes (baseline, v5_t1, v5_t2 must remain identical).
- Any schema changes to existing report payloads.
- Canonical surface expansion or new probe expansion (stay at 17 probes).
- Implementing Lane L2 (pair normalization) in this ticket.

## v5_T2 tolerance contract (pinned)

From `BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`:
- `toyh_tolerance = 1e-15`
- `phase_anchor_tolerance = 2e-08`
- `current_anchor_tolerance = 2e-08`
- `current_anchor_min_response = 1.25e-08`

## Implementation approach (Lane L1)

Introduce a stabilized phase residual computation that avoids cancellation/branch artifacts.

Design constraints:
- Deterministic.
- Uses only pinned inputs already present in the probe surface (theta, grid_n, amplitude_scale, etc.).
- Must preserve the meaning of the phase invariance check (same invariant, new numerics).

Candidate techniques (one or combine; keep minimal):
1. Compare phase via unit phasors:
   - represent phase as `u = exp(i * phi)` and compare using `|u1 - u2|` or `1 - Re(conj(u1)*u2)`.
2. Deterministic unwrap/branch handling:
   - remove direct subtraction of near-equal angles; operate modulo `2π` via stable identities.
3. Residual normalization:
   - compute residual in a scale-free form where appropriate (but do not loosen thresholds).

Deliverable: a single stabilized function used under v5_T2 (or universally if safe).

## Required code changes (suggested targets)

Primary:
- `formal/python/tools/bridge_toyh_c6_phase_anchor.py` (or the module implementing phase invariance / anchor)
- Any shared Toy-H phase bridge module used by orthogonality evaluation.

Secondary:
- If pair bridge directly depends on phase comparator output, ensure it consumes the stabilized quantity without changing pair semantics.

## Tests (must add)

### T2 closure tests (new)
1. `test_bridge_program_v5_t2_phase_stabilized_restores_repro_capsule`
   - For each probe in `BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json["minimal_reproduction_probes"]`:
     - assert v5_T2 signatures become `P-P-P`
     - assert phase lanes reason codes become `PASS` (or your canonical pass codes)
     - assert `toyhg_pair_bridge` becomes pass-capable

2. `test_bridge_program_v5_t2_frontier_lock_after_l1`
   - Generate v5_T2 orthogonality + mismatch artifacts.
   - Assert `n_mismatch == 0`
   - Assert reason summary `reason_code == "none"` and suggested ticket complete marker.

### Negative-control preservation tests (must not change)
3. `test_bridge_program_v5_t2_negative_controls_preserved_phase_wrong_sign`
   - For v3 theta-set negatives (anchor_sign=-1.0), assert same pinned failure codes as before.

4. `test_bridge_program_v5_t2_negative_controls_preserved_grid_amplitude_scale`
   - For v4 grid-size negatives (amplitude_scale=1.1), assert same tolerance-based failure codes as before.

### Regression safety (optional but recommended)
5. `test_bridge_program_baseline_and_v5_t1_closure_unchanged_after_l1`
   - Ensure baseline and v5_t1 still yield `n_mismatch == 0`.

## Evidence wiring (must update)

Add new pytest node pointers to the orthogonality report evidence list so audit surfaces remain complete.

## Acceptance criteria

1. Under `v5_t2`, bridge-program mismatch report shows:
   - `n_mismatch == 0`
   - reason summary returns `reason_code == "none"`
2. Minimal reproduction capsule probes flip back to pass:
   - `baseline_all_pass`, `stress_toyh_phase_control`, `stress_toyh_current_control`, `stress_toyh_grid_size_n15` become `P-P-P` under v5_T2.
3. All pinned negative controls retain the same failure reason codes as before.
4. Baseline and v5_t1 closure remain intact.

## Stop conditions (must halt and reopen design)

Stop implementation and reopen design ticket if any occur:
- Pair-only failures appear under v5_t2 when phase lanes are pass-capable.
- Any negative control starts passing.
- Closure under v5_t2 can only be achieved by relaxing tolerances.
- The stabilized method introduces nondeterminism or dependence on unpinned inputs.

## Runbook (pinned)

- Regenerate:
  - `BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`
  - `BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT_v5_T2.json`
  - `BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY_v5_T2.json`
- Run:
  - `.\py.ps1 -m pytest formal/python/tests -k "bridge or state_theory_dag"`
