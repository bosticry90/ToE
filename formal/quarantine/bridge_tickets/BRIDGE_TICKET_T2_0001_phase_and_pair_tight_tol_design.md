# BRIDGE_TICKET_T2_0001 — v5_T2 phase+pair tight-tolerance frontier [DESIGN-ONLY]

Status: Design-only preimplementation (falsifiable plan; bounded)

Opened: 2026-02-05

## Bridge family taxonomy (governance; docs-only)

- Bridge class: tolerance_tightening_frontier_resolution
- Evidence strength: bounded_design_preimplementation
- Degrees of freedom: pinned v5 tolerance profile, pinned flipped probe set, pinned lane-level reason-code decomposition
- Falsification mode: design cannot separate pure tolerance brittleness from true dual-root bridge mismatch on pinned v5_T2 frontier
- Non-implication clause: design only; no runtime bridge implementation or physics claim

## Triggering evidence (pinned)

Source artifacts:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY_v5_T2.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT_v5_T2.json`
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST.json`

Pinned trigger values:
- `recommended_next_target.reason_code = mismatch_phase_and_pair`
- `summary.n_mismatch = 13`
- `summary.reason_code_counts = {"mismatch_phase_and_pair": 13}`
- `expected_break_controls.v5_t1_closure_expected.passes = true`
- `expected_break_controls.v5_t2_expected_break.passes = true`
- `expected_break_controls.v5_t2_expected_break.n_formerly_pass_probes_flipped = 13`

## Problem statement (bounded)

Under tolerance profile `v5_t2` (tightest admissibility profile), probes that are `P-P-P` under baseline and `v5_t1` flip to `F-P-F` and are classified as `mismatch_phase_and_pair`. This is a compatibility failure under stricter tolerances, not a physics claim.

The design objective is to isolate whether this frontier is:
- pure tolerance brittleness (single-root: phase tolerance failure cascades to pair), or
- a real dual-root mismatch (phase and pair independently fail under the same profile).

## Pinned v5_T2 tolerance contract (must not be weakened)

From `BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`:
- `toyh_tolerance = 1e-15`
- `phase_anchor_tolerance = 2e-08`
- `current_anchor_tolerance = 2e-08`
- `current_anchor_min_response = 1.25e-08`

## Minimal reproduction capsule reference

- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`

The pinned minimal set includes four probes:
- `baseline_all_pass`
- `stress_toyh_phase_control`
- `stress_toyh_current_control`
- `stress_toyh_grid_size_n15`

Each flips `P-P-P -> F-P-F` under `v5_t2`, with:
- `toyh_phase.reason_code = FAIL_PHASE_INVARIANCE_TOL`
- `toyh_phase_anchor.reason_code = FAIL_PHASE_INVARIANCE_TOL`
- `toyhg_pair_bridge.reason_code = FAIL_PAIR_PHASE_MISMATCH`

## Goals (design-only done state)

1. Produce a deterministic decomposition that labels the frontier as single-root vs dual-root on pinned probes.
2. Propose the smallest lane plan that can restore closure under `v5_t2` without loosening any `v5_t2` tolerances.
3. Keep current negative controls valid (wrong-anchor-sign failures and amplitude-scale invariance failures).

## Non-goals

- No tolerance loosening or profile rewrite.
- No canonical-surface expansion in this ticket.
- No schema changes.
- No implementation lane in this ticket.

## Diagnostic decomposition plan

### D1 — Minimal failing probe partition

Use `BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json` (baseline) and `BRIDGE_PROGRAM_ORTHOGONALITY_REPORT_v5_T2.json`:
- Select probes where baseline signature is `P-P-P` and `v5_t2` signature is not `P-P-P`.
- Partition by channel failure pattern:
  - phase-only fail
  - pair-only fail
  - both fail

Pinned current result (from reproduction capsule):
- `phase-only = 0`
- `pair-only = 0`
- `both-fail = 13`

### D2 — Causality classification (single-root vs dual-root)

Apply deterministic classifier in:
- `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_CAUSALITY_CLASSIFIER.md`

Pinned current classification:
- `single_root_phase_to_pair` on all 13 flipped probes
- Evidence: pair lane reason code is uniformly `FAIL_PAIR_PHASE_MISMATCH` while current and Toy-G bridge outcomes remain pass-capable.

### D3 — Tolerance sensitivity localization

Track per failing probe:
- effective v5 tolerances
- lane-level reason codes for `toyh_phase`, `toyh_phase_anchor`, `toyh_current`, `toyh_current_anchor`, `toyhg_pair_bridge`

Pinned current result:
- failure concentration is on phase invariance tolerance (`FAIL_PHASE_INVARIANCE_TOL`) with pair fallout (`FAIL_PAIR_PHASE_MISMATCH`).

## Candidate solution directions (design)

### S1 — Tight-tolerance stabilized phase observable lane (preferred)

Add a new phase-stabilized bridge lane that computes the same conceptual phase invariant with numerically stable representation under `1e-15` tolerances, then feeds pair compatibility.

Acceptance targets:
- restore phase pass on baseline/T1-pass probes under `v5_t2` without changing tolerance values
- preserve existing negative controls and reason codes

### S2 — Tolerance-aware pair comparator lane (fallback if dual-root found)

Only if D2 shows pair failures independent of phase stabilization:
- add a profile-aware pair comparator lane using normalized margins consistent with `v5_t2`.

### S3 — Two-stage admissibility gate (last resort)

Use only if gate-order sensitivity is demonstrated:
- Stage 1 raw observable computation
- Stage 2 profile-specific admissibility decision

## Proposed design artifacts

1. `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json`
2. `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_CAUSALITY_CLASSIFIER.md`
3. `formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_LANE_PLAN.md`

## Acceptance criteria (design-only)

- Triggering evidence and exact artifact paths are pinned.
- D1-D3 decomposition is specified and reproducible.
- At least one viable lane plan is documented with bounded acceptance tests.
- No implementation changes are required to close this design ticket.

## Exit condition

Open implementation ticket only after this design is accepted:
- recommended next implementation: `BRIDGE_TICKET_TOYH_0005` (or equivalent namespace) for S1 phase-stabilized lane.

